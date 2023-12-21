with (import <nixpkgs> {});
let
  elementsd-simplicity = elementsd.overrideAttrs (_: rec {
    version = "unstable-2023-11-22";
    src = fetchFromGitHub {
      owner = "ElementsProject";
      repo = "elements";
      rev = "174c46baecd7b180cda977827886833840ac49e3"; # <-- update this to latest `simplicity` branch: https://github.com/ElementsProject/elements/commits/simplicity
      sha256 = "sha256-kSN3Rj7YdFoBibOFdKq7f6RTaVamN1dFjuL3wPOu5Kw="; # <-- overwrite this, rerun and place the expected hash
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
