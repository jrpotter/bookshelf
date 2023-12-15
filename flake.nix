{
  description = "";

  inputs = {
    flake-compat.url = "https://flakehub.com/f/edolstra/flake-compat/1.tar.gz";
    flake-utils.url = "github:numtide/flake-utils";
    nixpkgs.url = "github:NixOS/nixpkgs/nixos-unstable";
  };

  outputs = { self, nixpkgs, flake-utils, ... }:
    flake-utils.lib.eachDefaultSystem (system:
      let
        pkgs = nixpkgs.legacyPackages.${system};
        manifest = import ./lake-manifest.nix { inherit pkgs; };
        scheme-custom = with pkgs; (texlive.combine {
          inherit (texlive) scheme-basic
            bigfoot
            comment
            enumitem
            environ
            etoolbox
            fontawesome5
            jknapltx
            mathabx
            mathabx-type1
            metafont
            ncctools
            pgf
            rsfs
            soul
            stmaryrd
            tcolorbox
            xcolor;
        });
      in
      {
        packages = {
          app = pkgs.stdenv.mkDerivation {
            pname = "bookshelf";
            version = "0.1.0";
            src = ./.;
            nativeBuildInputs = with pkgs; [
              git
              lean4
              scheme-custom
            ];
            buildPhase = ''
              mkdir -p .lake/packages
              ${pkgs.lib.foldlAttrs (s: key: val: s + ''
                cp -a ${val}/src .lake/packages/${key}
                chmod 755 .lake/packages/${key}/{,.git}
              '') "" manifest}

              export GIT_ORIGIN_URL="https://github.com/jrpotter/bookshelf.git"
              export GIT_REVISION="${self.rev or "dirty"}"
              lake build Bookshelf:docs

              find .lake/build/doc \
                \( -name "*.html.trace" -o -name "*.html.hash" \) \
                -exec rm {} +
            '';
            installPhase = ''
              mkdir $out
              cp -a .lake/build/doc/* $out
            '';
          };

          default = self.packages.${system}.app;
        };

        devShells.default = pkgs.mkShell {
          packages = with pkgs; [
            lean4
            python3
            scheme-custom
          ];
        };
      });
}
