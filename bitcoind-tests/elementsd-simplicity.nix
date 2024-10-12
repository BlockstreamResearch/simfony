{ pkgs
}:
pkgs.elementsd.overrideAttrs (_: {
  version = "liquid-testnet-2024-10-08";
  src = pkgs.fetchFromGitHub {
    owner = "ElementsProject";
    repo = "elements";
    rev = "f957d3cde17c85afb18c6747f9c0b4fcb599f19a"; # <-- update this to latest `simplicity` branch: https://github.com/ElementsProject/elements/commits/simplicity
    sha256 = "sha256-XzdfbrQ7s4PfM5N00oP1jo5BNmD4WUMUe79QsTxsL4s="; # <-- overwrite this, rerun and place the expected hash
  };
  withWallet = true;
  withGui = false;
  doCheck = false;
})
