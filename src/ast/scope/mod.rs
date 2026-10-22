mod imports;
mod locals;
mod program_inputs;

use std::collections::HashMap;
use std::convert::Infallible;
use std::sync::Arc;

use crate::debug::TrackedCallName;
use crate::error::{Diagnostic, DiagnosticManager, Error, Span};
use crate::parse::{self, Visibility};
use crate::str::{AliasName, FunctionName, Identifier, ModuleName};
use crate::types::{AliasedType, EnumInfo, EnumVariantInfo, ResolvedType};
use crate::TemplateProgramWitness;

use self::locals::Locals;
use self::program_inputs::ProgramInputs;
use super::recovery::{mentions_never, Failure};
use super::{CustomFunction, ElementsJetHinter, Expression, JetHinter, Program};

/// A single module namespace. Handles arbitrary nesting via `submodules`.
#[derive(Clone, Debug, Eq, PartialEq, Default)]
struct ModuleScope {
    aliases: HashMap<AliasName, (ResolvedType, Visibility)>,
    functions: HashMap<FunctionName, (CustomFunction, Visibility)>,
    /// Nested inling `mod` blocks, each becoming a child scope.
    submodules: HashMap<ModuleName, (ModuleScope, Visibility)>,
}

/// Scope for generating the abstract syntax tree.
///
/// The scope is used for:
/// 1. Assigning types to each variable
/// 2. Resolving type aliases
/// 3. Assigning types to each witness expression
/// 4. Resolving calls to custom functions
pub(super) struct Scope {
    /// Current position in the module tree. Push on `mod` enter, pop on exit.
    /// Empty path means we are at the root (main file) scope.
    pub(super) module_path: Vec<ModuleName>,

    /// Global scope where items from the main file that live at the root level.
    root: ModuleScope,

    locals: Locals,
    inputs: ProgramInputs,

    is_main: bool,
    /// Allow enum constructions to name an enum by its declared name even
    /// when that name is not an alias in scope. Enabled only for value
    /// parsing (witness and argument files), which runs without a scope.
    pub(super) unscoped_enum_names: bool,
    pub(super) jet_hinter: Box<dyn JetHinter>,
    /// Errors reported during analysis that did not stop it.
    pub(super) diagnostics: Vec<Diagnostic>,
}

impl Default for Scope {
    fn default() -> Self {
        Self::new(
            // TODO: Should be passed in global configuration
            Box::new(ElementsJetHinter),
        )
    }
}

impl Scope {
    pub(super) fn new(jet_hinter: Box<dyn JetHinter>) -> Self {
        Self {
            module_path: Vec::new(),
            root: ModuleScope::default(),
            locals: Locals::default(),
            inputs: ProgramInputs::default(),
            is_main: false,
            unscoped_enum_names: false,
            jet_hinter,
            diagnostics: Vec::new(),
        }
    }

    /// Record an error without stopping analysis.
    ///
    /// A failure that was already reported is not recorded again.
    pub(super) fn report(&mut self, failure: impl Into<Failure>) {
        if let Failure::New(diagnostic) = failure.into() {
            // Like rustc, an error about a type with `!` is left until the error
            // that created `!` is fixed.
            if !mentions_never(diagnostic.error()) {
                self.diagnostics.push(diagnostic);
            }
        }
    }

    /// Report the error of a failed check that does not prevent building the node.
    pub(super) fn report_err(&mut self, result: Result<(), Diagnostic>) {
        if let Err(error) = result {
            self.report(error);
        }
    }

    /// Analyze every item, even if some of them fail.
    ///
    /// Every error is reported as soon as it is found. If any item fails,
    /// the caller receives [`Failure::Reported`] and stops as before.
    pub(super) fn analyze_all<A, T>(
        &mut self,
        items: impl IntoIterator<Item = A>,
        mut analyze: impl FnMut(A, &mut Self) -> Result<T, Failure>,
    ) -> Result<Vec<T>, Failure> {
        let mut results = Vec::new();
        let mut failed = false;

        for item in items {
            match analyze(item, self) {
                Ok(result) => results.push(result),
                Err(failure) => {
                    self.report(failure);
                    failed = true;
                }
            }
        }

        if failed {
            Err(Failure::Reported)
        } else {
            Ok(results)
        }
    }

    /// Scope for parsing values from witness and argument files: empty,
    /// except that enum constructions may name an enum by its declared name.
    pub(super) fn for_value_parsing() -> Self {
        Self {
            unscoped_enum_names: true,
            ..Self::default()
        }
    }

    pub(super) fn is_outside_function(&self) -> bool {
        // Entering a function body pushes a new map of variables,
        // and every nested block inside it pushes another one.
        // The stack is empty only when we are not inside any function.
        self.locals.depth() == 0
    }

    /// Analyze within a nested block scope and restore the previous scope afterwards
    pub(super) fn in_block<T>(&mut self, analyze: impl FnOnce(&mut Self) -> T) -> T {
        let outer_depth = self.locals.depth();
        self.locals.enter_block();
        let result = analyze(self);
        debug_assert_eq!(
            self.locals.depth(),
            outer_depth + 1,
            "Unbalanced nested block scopes"
        );
        self.locals.exit_block();
        debug_assert_eq!(
            self.locals.depth(),
            outer_depth,
            "Block scope was not restored"
        );
        result
    }

    /// Analyze within a function scope and restore the outside-function state afterwards
    pub(super) fn in_function<T>(&mut self, analyze: impl FnOnce(&mut Self) -> T) -> T {
        debug_assert!(self.is_outside_function(), "Already inside a function body");
        let result = self.in_block(analyze);
        debug_assert!(
            self.is_outside_function(),
            "Function scope was not restored"
        );
        result
    }

    /// Analyze within a match-arm scope and restore the enclosing scope afterwards
    pub(super) fn in_match_arm<T>(&mut self, analyze: impl FnOnce(&mut Self) -> T) -> T {
        self.in_block(analyze)
    }

    /// Push the scope of the main function onto the stack.
    ///
    /// ## Panics
    ///
    /// - Already inside the main function.
    /// - Already inside a function body.
    fn enter_main(&mut self) {
        assert!(!self.is_main, "Already inside main function");
        assert!(self.is_outside_function(), "Already inside a function body");
        self.locals.enter_block();
        self.is_main = true;
    }

    /// Analyze within the main-function scope and restore the outside-function state afterwards.
    pub(super) fn in_main<T>(&mut self, analyze: impl FnOnce(&mut Self) -> T) -> T {
        self.enter_main();
        let result = analyze(self);

        debug_assert!(self.is_main, "Main scope was exited during analysis");
        debug_assert_eq!(
            self.locals.depth(),
            1,
            "Unbalanced nested blocks in main scope"
        );

        self.exit_main();
        debug_assert!(!self.is_main, "Main scope was not restored");
        debug_assert!(
            self.is_outside_function(),
            "Main function scope was not restored"
        );
        result
    }

    /// Pop the scope of the main function from the stack.
    ///
    /// ## Panics
    ///
    /// - Not inside the main function.
    /// - Unclosed nested blocks remain.
    fn exit_main(&mut self) {
        assert!(self.is_main, "Current scope is not inside main function");
        self.locals.exit_block();
        self.is_main = false;
        assert!(
            self.is_outside_function(),
            "Current scope is not nested in topmost scope"
        )
    }

    /// Enter a named module, pushing it onto the module path.
    ///
    /// ## Errors
    ///
    /// * [`Error::ModuleRedefined`] A module with this name is already defined in the current scope.
    fn enter_module(&mut self, name: ModuleName, visibility: Visibility) -> Result<(), Error> {
        let current = self.current_module_mut();
        if current.submodules.contains_key(&name) {
            return Err(Error::ModuleRedefined { name });
        }

        current
            .submodules
            .insert(name.clone(), (ModuleScope::default(), visibility));
        self.module_path.push(name);
        Ok(())
    }

    /// Analyze within a named module and restore the enclosing module afterwards.
    pub(super) fn in_module<T>(
        &mut self,
        name: ModuleName,
        visibility: Visibility,
        analyze: impl FnOnce(&mut Self) -> T,
    ) -> Result<T, Error> {
        let outer_depth = self.module_path.len();
        self.enter_module(name.clone(), visibility)?;
        let result = analyze(self);
        debug_assert_eq!(
            self.module_path.len(),
            outer_depth + 1,
            "Unbalanced nested module scopes"
        );
        debug_assert_eq!(
            self.module_path.last(),
            Some(&name),
            "Current module changed during analysis"
        );
        self.exit_module();
        debug_assert_eq!(
            self.module_path.len(),
            outer_depth,
            "Module scope was not restored"
        );
        Ok(result)
    }

    /// Exit the current module, popping it from the module path.
    ///
    /// ## Panics
    ///
    /// Not inside any module.
    fn exit_module(&mut self) {
        self.module_path.pop().expect("Not inside any module");
    }

    /// This allows us to perform read-only checks (like redefinitions) and
    /// call `resolve` without taking a premature mutable borrow of `self`.
    fn current_module(&self) -> &ModuleScope {
        self.module_path.iter().fold(&self.root, |scope, segment| {
            &scope.submodules.get(segment).expect("Module not found").0
        })
    }

    /// We use iterations and `O(N)` algorithm, because nested block are not so deep.
    /// It will be strange to see 100 nested blocks, so common `.fold()` will be enough for that.
    fn current_module_mut(&mut self) -> &mut ModuleScope {
        self.module_path
            .iter()
            .fold(&mut self.root, |scope, segment| {
                &mut scope
                    .submodules
                    .get_mut(segment)
                    .expect("Module not found")
                    .0
            })
    }

    /// Insert a variable into the current block.
    ///
    /// ## Panics
    ///
    /// - No active block.
    pub(super) fn insert_variable(&mut self, identifier: Identifier, ty: ResolvedType) {
        self.locals.insert(identifier, ty);
    }

    /// Get the type of the variable.
    pub(super) fn get_variable(&self, identifier: &Identifier) -> Option<&ResolvedType> {
        self.locals.get(identifier)
    }

    /// Retrieves the resolved type of a type alias in the current module scope.
    ///
    /// ## Errors
    ///
    /// * [`Error::UndefinedAlias`]: The alias is not defined in the current scope.
    pub(super) fn get_alias(&self, name: &AliasName) -> Result<ResolvedType, Error> {
        self.current_module()
            .aliases
            .get(name)
            .map(|(ty, _)| ty.clone())
            .ok_or_else(|| Error::UndefinedAlias { name: name.clone() })
    }

    /// Resolve a type with aliases to a type without aliases.
    ///
    /// ## Errors
    ///
    /// * [`Error::UndefinedAlias`]: The alias is not found in the global registry.
    pub(super) fn resolve(&self, ty: &AliasedType) -> Result<ResolvedType, Error> {
        ty.resolve(|name| self.get_alias(name))
    }

    /// Resolve a type, reporting every undefined alias and replacing it with `!`.
    ///
    /// This is the only place where analysis creates `!`, so every `!` has a reported error.
    pub(super) fn resolve_or_never(
        &mut self,
        ty: &AliasedType,
        span: impl Into<Span>,
    ) -> ResolvedType {
        let mut errors = Vec::new();
        let resolved = ty
            .resolve(|name| {
                Ok::<_, Infallible>(self.get_alias(name).unwrap_or_else(|error| {
                    errors.push(error);
                    ResolvedType::never()
                }))
            })
            .unwrap_or_else(|never| match never {});

        let span = span.into();
        for error in errors {
            self.report(error.with_span(span));
        }

        resolved
    }

    /// Error if `name` is already defined as an alias in the current module.
    fn check_alias_free(&self, name: &AliasName) -> Result<(), Error> {
        if self.current_module().aliases.contains_key(name) {
            return Err(Error::RedefinedAlias { name: name.clone() });
        }

        Ok(())
    }

    /// Insert a type alias into the current module scope.
    ///
    /// ## Errors
    ///
    /// * [`Error::RedefinedAlias`]: The alias name is already defined in the current scope.
    pub(super) fn insert_alias(&mut self, alias: parse::TypeAlias) -> Result<(), Error> {
        self.check_alias_free(alias.name())?;

        let resolved = self.resolve_or_never(alias.ty(), &alias);

        self.current_module_mut()
            .aliases
            .insert(alias.name().clone(), (resolved, alias.visibility().clone()));

        Ok(())
    }

    /// Insert an enum declaration into the current module.
    ///
    /// An enum is a type alias for a nominal enum type, so its name resolves as a type
    /// and its identity travels wherever the alias is imported.
    ///
    /// Enums may only be declared at the top level of the program's own files
    /// (the parser rejects declarations inside `mod` blocks, the driver rejects them in dependency files),
    /// so the bare name is unique program-wide and identifies the enum in the ABI.
    ///
    /// ## Errors
    ///
    /// * [`Error::RedefinedAlias`]: The name is already defined in the current module.
    pub(super) fn insert_enum(
        &mut self,
        name: AliasName,
        visibility: Visibility,
        variants: Arc<[EnumVariantInfo]>,
    ) -> Result<(), Error> {
        self.check_alias_free(&name)?;

        let info = EnumInfo::new(Arc::clone(name.as_inner()), variants);
        let resolved = ResolvedType::enumeration(info);

        self.current_module_mut()
            .aliases
            .insert(name, (resolved, visibility));

        Ok(())
    }

    pub(super) fn insert_parameter(
        &mut self,
        name: TemplateProgramWitness,
        ty: ResolvedType,
    ) -> Result<(), Error> {
        self.inputs.insert_parameter(name, ty)
    }

    /// Insert a witness into the global map.
    ///
    /// ## Errors
    ///
    /// * [`Error::WitnessOutsideMain`] The current scope is not inside the main function.
    /// * [`Error::WitnessReused`] A witness with the same name has already been defined.
    pub(super) fn insert_witness(
        &mut self,
        name: TemplateProgramWitness,
        ty: ResolvedType,
    ) -> Result<(), Error> {
        if !self.is_main {
            return Err(Error::WitnessOutsideMain);
        }

        self.inputs.insert_witness(name, ty)
    }

    /// Consume the scope and build the analyzed program with the given `main` body.
    pub(super) fn try_into_program(
        mut self,
        main: Result<Expression, Failure>,
        diagnostics: &mut DiagnosticManager,
    ) -> Option<Program> {
        let main = main.map_err(|failure| self.report(failure));
        match main {
            Ok(main) if self.diagnostics.is_empty() => Some(self.inputs.into_program(main)),
            _ => {
                diagnostics.extend(self.diagnostics);
                None
            }
        }
    }

    /// Insert a custom function into the global map.
    ///
    /// ## Errors
    ///
    /// * [`Error::FunctionRedefined`] The function has already been defined.
    pub(super) fn insert_function(
        &mut self,
        name: FunctionName,
        visibility: Visibility,
        function: CustomFunction,
    ) -> Result<(), Error> {
        if self.current_module().functions.contains_key(&name) {
            return Err(Error::FunctionRedefined { name });
        }

        self.current_module_mut()
            .functions
            .insert(name, (function, visibility));
        Ok(())
    }

    /// Retrieves the definition of a custom function, enforcing strict error prioritization.
    ///
    /// ## Errors
    ///
    /// * [`Error::FunctionUndefined`]: The function is not found in the global registry.
    pub(super) fn get_function(&self, name: &FunctionName) -> Result<CustomFunction, Error> {
        self.current_module()
            .functions
            .get(name)
            .map(|(func, _)| func.clone())
            .ok_or_else(|| Error::FunctionUndefined { name: name.clone() })
    }

    pub(super) fn track_call<S: AsRef<Span>>(&mut self, span: &S, name: TrackedCallName) {
        self.inputs.track_call(span, name);
    }
}

#[cfg(test)]
mod scope_balance_tests {
    use super::*;

    #[test]
    fn scopes_are_restored_after_failed_analysis() {
        let mut scope = Scope::new(Box::new(ElementsJetHinter));

        scope.locals.enter_block();
        let result: Result<(), ()> = scope.in_block(|_| Err(()));
        assert!(result.is_err());
        assert_eq!(scope.locals.depth(), 1);
        scope.locals.exit_block();

        let result: Result<(), ()> = scope.in_main(|_| Err(()));
        assert!(result.is_err());
        assert!(!scope.is_main);
        assert!(scope.is_outside_function());

        let result: Result<(), ()> = scope
            .in_module(
                ModuleName::from_str_unchecked("module"),
                Visibility::Private,
                |_| Err(()),
            )
            .expect("module entry succeeds");
        assert!(result.is_err());
        assert!(scope.module_path.is_empty());
    }
}
