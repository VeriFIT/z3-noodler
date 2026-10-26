# Nix flake of Z3-Noodler: formatting, checks, packages, and development shells.
#
# All recipes run in the repository root, where the flake lives.

set working-directory := '..'

# Format the Nix files with treefmt.
[default]
fmt *ARGS:
	nix fmt {{ ARGS }}

# Evaluate and build all flake outputs.
check:
	nix flake check

# Build a flake package, e.g. 'just nix build noodlerClang'.
build PACKAGE="default":
	nix build '.#{{ PACKAGE }}'

# Enter a development shell, e.g. 'just nix develop clang'.
develop SHELL="default":
	nix develop '.#{{ SHELL }}'

# Update all flake inputs.
update:
	nix flake update
