{
  description = "A Nix flake for Z3-Noodler: An SMT solver for string constraints";

  inputs = {
    nixpkgs.url = "github:NixOS/nixpkgs/nixos-unstable";
    omniflake = {
      url = "github:fzakaria/omniflake";
      inputs.nixpkgs.follows = "nixpkgs";
    };
    # Keep in sync with the Mata 'GIT_TAG' in CMakeLists.txt.
    mata = {
      url = "github:VeriFIT/mata/v1.32.37";
      inputs.nixpkgs.follows = "nixpkgs";
    };
  };

  outputs = inputs: inputs.omniflake.unified.flake-parts.lib.mkFlake { inherit inputs; } ./nix;
}
