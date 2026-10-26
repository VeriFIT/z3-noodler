{
  perSystem = {
    treefmt = {
      # Not '.git/config': in a git worktree or a jj workspace '.git' is a file, so treefmt would walk up to and
      #  format the enclosing main checkout instead.
      projectRootFile = "flake.nix";
      programs.nixfmt.enable = true;
    };
  };
}
