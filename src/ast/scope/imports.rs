use std::collections::hash_map::Entry;
use std::collections::HashMap;

use crate::driver::{CRATE_STR, MAIN_STR};
use crate::error::Error;
use crate::parse::{self, UseDecl, Visibility};
use crate::str::{ModuleName, SymbolName};

use super::{ModuleScope, Scope};

impl Scope {
    // TODO: Consider to optimize it (we definitely can do it)
    /// Resolves a `use` declaration by navigating the module tree, checking visibility,
    /// and importing matching items into the current scope.
    ///
    /// ## Errors
    ///
    /// * [`Error::MissingCrateKeyword`] The import path does not start with the `crate` keyword.
    /// * [`Error::ModuleNotFound`] A module segment in the target path does not exist.
    /// * [`Error::ModuleIsPrivate`] Attempted to navigate into a private module from an unauthorized scope.
    /// * [`Error::MainCannotBeAlias`] Attempted to alias an imported item to the reserved `main` identifier.
    /// * May also return errors propagated from item collection and insertion, such as [`Error::PrivateItem`] or [`Error::RedefinedItem`].
    pub(in crate::ast) fn resolve_use(&mut self, use_decl: &UseDecl) -> Result<(), Error> {
        let path = use_decl.path();
        if path.first().map(|id| id.as_str()) != Some(CRATE_STR) {
            return Err(Error::MissingCrateKeyword);
        }

        let use_vis = use_decl.visibility().clone();
        let use_decl_items = match use_decl.items() {
            parse::UseItems::Single(elem) => std::slice::from_ref(elem),
            parse::UseItems::List(elems) => elems.as_slice(),
        };

        // Phase 1: navigate to target and collect items. Immutable borrow, dropped at end of block
        // Vec<(ProcessedAlias, ProcessedFunction, ProcessedModule)>
        // where each is Result<(Key, (Value, Visibility)), Error>
        let collected: Vec<_> = {
            // TODO: Part, that can be optimized
            // How many segments do the caller's path and the target's path have in common?
            let shared_prefix_len = self
                .module_path
                .iter()
                .zip(&path[1..])
                .take_while(|(curr, nav)| curr.as_str() == nav.as_str())
                .count();

            let mut target_scope = &self.root;

            for (ind, segment) in path[1..].iter().enumerate() {
                let name = ModuleName::from_ident(segment);

                let (inner, visibility) = target_scope
                    .submodules
                    .get(&name)
                    .ok_or_else(|| Error::ModuleNotFound { name: name.clone() })?;

                if matches!(visibility, Visibility::Private) && shared_prefix_len < ind {
                    return Err(Error::ModuleIsPrivate { name });
                }

                target_scope = inner;
            }

            let mut collected = Vec::with_capacity(use_decl_items.len());
            for (name, aliased) in use_decl_items {
                if aliased.as_ref().is_some_and(|a| a == MAIN_STR) {
                    return Err(Error::MainCannotBeAlias);
                }

                let local_name = aliased.as_ref().unwrap_or(name);

                let alias_res =
                    Self::try_collect_item(name, local_name, &target_scope.aliases, &use_vis);
                let func_res =
                    Self::try_collect_item(name, local_name, &target_scope.functions, &use_vis);
                let mod_res =
                    Self::try_collect_item(name, local_name, &target_scope.submodules, &use_vis);

                collected.push((alias_res, func_res, mod_res));
            }
            collected
        };

        // Phase 2: validate against existing names and stage the complete import.
        // Failed declarations discard these maps without changing the module tree.
        let current = self.current_module();
        let mut pending = ModuleScope::default();
        for (alias_res, func_res, mod_res) in collected {
            Self::resolve_processing_use_items_error(&[
                Self::stage_collected(alias_res, &current.aliases, &mut pending.aliases),
                Self::stage_collected(func_res, &current.functions, &mut pending.functions),
                Self::stage_collected(mod_res, &current.submodules, &mut pending.submodules),
            ])?;
        }

        // Phase 3: commit because every item was resolved successfully
        let current = self.current_module_mut();
        current.aliases.extend(pending.aliases);
        current.functions.extend(pending.functions);
        current.submodules.extend(pending.submodules);

        Ok(())
    }

    /// Attempts to find `name` in `target_map` and prepare it for import into another scope.
    ///
    /// ## Errors
    ///
    /// * [`Error::UnresolvedItem`] The requested `name` was not found in the `target_map`.
    /// * [`Error::PrivateItem`] The requested item exists in the map, but its visibility is restricted to private.
    fn try_collect_item<K, V>(
        name: &SymbolName,
        local_name: &SymbolName,
        target_map: &HashMap<K, (V, Visibility)>,
        use_vis: &Visibility,
    ) -> Result<(K, (V, Visibility)), Error>
    where
        K: Eq + std::hash::Hash + From<SymbolName> + Clone,
        V: Clone,
    {
        let (value, vis) =
            target_map
                .get(&K::from(name.clone()))
                .ok_or_else(|| Error::UnresolvedItem {
                    name: name.to_string(),
                })?;

        if matches!(vis, Visibility::Private) {
            return Err(Error::PrivateItem {
                name: name.to_string(),
            });
        }

        Ok((
            K::from(local_name.clone()),
            (value.clone(), use_vis.clone()),
        ))
    }

    /// Stages a collected item, checking existing bindings and earlier staged names.
    ///
    /// ## Errors
    ///
    /// * [`Error::RedefinedItem`] An item with the same name is already defined in the target scope.
    /// * Propagates any upstream resolution error passed into the `res` argument.
    fn stage_collected<K, V>(
        res: Result<(K, (V, Visibility)), Error>,
        existing: &HashMap<K, (V, Visibility)>,
        pending: &mut HashMap<K, (V, Visibility)>,
    ) -> Result<(), Error>
    where
        K: Eq + std::hash::Hash + std::fmt::Display,
    {
        res.and_then(|(k, v)| {
            if existing.contains_key(&k) {
                return Err(Error::RedefinedItem {
                    name: k.to_string(),
                });
            }
            match pending.entry(k) {
                Entry::Occupied(entry) => Err(Error::RedefinedItem {
                    name: entry.key().to_string(),
                }),
                Entry::Vacant(entry) => {
                    entry.insert(v);
                    Ok(())
                }
            }
        })
    }

    // TODO: Consider to use better error handling
    /// Evaluates the results of attempting to collect an item from multiple namespaces
    /// (aliases, functions, submodules) and resolves the final error state.
    ///
    /// ## Errors
    ///
    /// * Returns a specific error (e.g., [`Error::PrivateItem`], [`Error::RedefinedItem`]) if one occurred.
    /// * Returns a fallback [`Error::UnresolvedItem`] if the item could not be found in any of the checked namespaces.
    fn resolve_processing_use_items_error(results: &[Result<(), Error>]) -> Result<(), Error> {
        if results.iter().any(|res| res.is_ok()) {
            return Ok(());
        }

        let errors: Vec<&Error> = results
            .iter()
            .filter_map(|res| res.as_ref().err())
            .collect();

        if let Some(&specific_err) = errors
            .iter()
            .find(|e| !matches!(e, Error::UnresolvedItem { .. }))
        {
            return Err(specific_err.clone());
        }

        // Fallback to the first `UnresolvedItem` error
        Err(errors[0].clone())
    }
}

#[cfg(test)]
mod transactional_use_tests {
    use super::*;
    use crate::parse::ParseFromStr;
    use crate::str::AliasName;
    use crate::types::{ResolvedType, TypeConstructible};

    fn resolve(scope: &mut Scope, source: &str) -> Result<(), Error> {
        let program = parse::Program::parse_from_str(source).unwrap();
        let parse::Item::Use(decl) = &program.items()[0] else {
            panic!("expected use declaration");
        };
        scope.resolve_use(decl)
    }

    fn scope() -> Scope {
        let mut scope = Scope::default();
        scope
            .enter_module(ModuleName::from_str_unchecked("source"), Visibility::Public)
            .unwrap();

        scope.current_module_mut().aliases.insert(
            AliasName::from_str_unchecked("Good"),
            (ResolvedType::u32(), Visibility::Public),
        );

        scope.current_module_mut().aliases.insert(
            AliasName::from_str_unchecked("Secret"),
            (ResolvedType::u16(), Visibility::Private),
        );

        scope.exit_module();
        scope
    }

    #[test]
    fn failed_imports_preserve_the_complete_module_tree() {
        for (source, expected) in [
            (
                "use crate::source::{Good, Missing};",
                Error::UnresolvedItem {
                    name: "Missing".into(),
                },
            ),
            (
                "use crate::source::{Good, Secret};",
                Error::PrivateItem {
                    name: "Secret".into(),
                },
            ),
            (
                "use crate::source::{Good as Same, Good as Same};",
                Error::RedefinedItem {
                    name: "Same".into(),
                },
            ),
            (
                "use crate::source::{Good, Good as main};",
                Error::MainCannotBeAlias,
            ),
            (
                "use crate::source::{Good, Good as Taken};",
                Error::RedefinedItem {
                    name: "Taken".into(),
                },
            ),
        ] {
            for nested in [false, true] {
                let mut scope = scope();
                if nested {
                    scope
                        .enter_module(
                            ModuleName::from_str_unchecked("consumer"),
                            Visibility::Private,
                        )
                        .unwrap();
                }

                scope.current_module_mut().aliases.insert(
                    AliasName::from_str_unchecked("Taken"),
                    (ResolvedType::u8(), Visibility::Private),
                );

                let before = scope.root.clone();
                let path = scope.module_path.clone();
                let error = resolve(&mut scope, source).expect_err(source);

                assert_eq!(error.to_string(), expected.to_string(), "{source}");
                assert_eq!(scope.root, before, "failed import mutated scope: {source}");
                assert_eq!(scope.module_path, path, "{source}");

                resolve(&mut scope, "use crate::source::Good;").unwrap();
            }
        }
    }

    #[test]
    fn successful_import_commits_all_namespaces_and_visibility() {
        let mut scope = scope();
        let source = &mut scope
            .root
            .submodules
            .get_mut(&ModuleName::from_str_unchecked("source"))
            .unwrap()
            .0;
        source.submodules.insert(
            ModuleName::from_str_unchecked("Good"),
            (ModuleScope::default(), Visibility::Public),
        );
        resolve(&mut scope, "pub use crate::source::Good as Renamed;").unwrap();

        assert_eq!(
            scope
                .root
                .aliases
                .get(&AliasName::from_str_unchecked("Renamed")),
            Some(&(ResolvedType::u32(), Visibility::Public))
        );
        assert!(matches!(
            scope
                .root
                .submodules
                .get(&ModuleName::from_str_unchecked("Renamed")),
            Some((_, Visibility::Public))
        ));
    }
}
