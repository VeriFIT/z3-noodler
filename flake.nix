{
  description = "A Nix flake for Z3-Noodler: An SMT solver for string constraints";

  inputs = {
    nixpkgs.url = "github:NixOS/nixpkgs/nixos-unstable";
    omniflake = {
      url = "github:fzakaria/omniflake";
      inputs.nixpkgs.follows = "nixpkgs";
    };
    # Must match the Mata 'GIT_TAG' in CMakeLists.txt; evaluation fails otherwise (see nix/noodler.nix).
    mata = {
      url = "github:VeriFIT/mata/issue-975-noodle-order";
      inputs.nixpkgs.follows = "nixpkgs";
    };
  };

  outputs = inputs: inputs.omniflake.unified.flake-parts.lib.mkFlake { inherit inputs; } ./nix;
}
