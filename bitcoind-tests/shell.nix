with (import <nixpkgs> {});
let
  elementsd-simplicity = elementsd.overrideAttrs (_: rec {
    version = "unstable-2024-09-02";
    src = fetchFromGitHub {
      owner = "ElementsProject";
      repo = "elements";
      rev = "37c231153a9c61f02f932c2cb802656ae47cff32"; # <-- update this to latest `simplicity` branch: https://github.com/ElementsProject/elements/commits/simplicity
      sha256 = "sha256-QYywe7lfBQIjp7CecxA/6/XsWAOaBckGbT432Xe2ru0="; # <-- overwrite this, rerun and place the expected hash
    };
    withWallet = true;
    withGui = false;
    doCheck = false;
  });
in
  mkShell {
    buildInputs = [
      elementsd-simplicity
    ];
  }
