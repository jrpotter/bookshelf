{ pkgs }:
let
  fetchGitPackage = { pname, version, owner, repo, rev, hash }:
    pkgs.stdenv.mkDerivation {
      inherit pname version;
      src = pkgs.fetchgit {
        inherit rev hash;
        url = "https://github.com/${owner}/${repo}";
        # We need to keep this attribute enabled to prevent Lake from trying to
        # update the package. This attribute ensures the specified commit is
        # accessible at HEAD:
        # https://github.com/leanprover/lean4/blob/cddc8089bc736a1532d6092f69476bd2d205a9eb/src/lake/Lake/Load/Materialize.lean#L22
        leaveDotGit = true;
      };
      nativeBuildInputs = with pkgs; [ git ];
      # Lake will perform a compulsory check that `git remote get-url origin`
      # returns the value we set here:
      # https://github.com/leanprover/lean4/blob/cddc8089bc736a1532d6092f69476bd2d205a9eb/src/lake/Lake/Load/Materialize.lean#L54
      buildPhase = ''
        git remote add origin https://github.com/${owner}/${repo}
      '';
      installPhase = ''
        shopt -s dotglob
        mkdir -p $out/src
        cp -a . $out/src
      '';
    };
in
{
  CMark = fetchGitPackage {
    pname = "CMark";
    version = "main";
    owner = "xubaiw";
    repo = "CMark.lean";
    rev = "0077cbbaa92abf855fc1c0413e158ffd8195ec77";
    hash = "sha256-ge+9V4IsMdPwjhYu66zUUN6CK70K2BdMT98BzBV3a4c=";
  };

  Cli = fetchGitPackage {
    pname = "Cli";
    version = "main";
    owner = "leanprover";
    repo = "lean4-cli";
    rev = "a751d21d4b68c999accb6fc5d960538af26ad5ec";
    hash = "sha256-n+6x7ZhyKKiIMZ9cH9VV8zay3oTUlJojtxcLYsUwQPU=";
  };

  Qq = fetchGitPackage {
    pname = "Qq";
    version = "master";
    owner = "leanprover-community";
    repo = "quote4";
    rev = "d3a1d25f3eba0d93a58d5d3d027ffa78ece07755";
    hash = "sha256-l+X+Mi4khC/xdwQmESz8Qzto6noYqhYN4UqC+TVt3cs=";
  };

  UnicodeBasic = fetchGitPackage {
    pname = "UnicodeBasic";
    version = "main";
    owner = "fgdorais";
    repo = "lean4-unicode-basic";
    rev = "dc62b29a26fcc3da545472ab8ad2c98ef3433634";
    hash = "sha256-EimohrYMr01CnGx8xCg4q4XX663QuxKfpTDNnDnosO4=";
  };

  aesop = fetchGitPackage {
    pname = "aesop";
    version = "master";
    owner = "leanprover-community";
    repo = "aesop";
    rev = "c7cff4551258d31c0d2d453b3f9cbca757d445f1";
    hash = "sha256-uzkxE9XJ4y3WMtmiNQn2Je1hNkQ2FgE1/0vqz8f98cw=";
  };

  doc-gen4 = fetchGitPackage {
    pname = "doc-gen4";
    version = "main";
    owner = "jrpotter";
    repo = "bookshelf-doc";
    rev = "9bd217dc37ea79a3f118a313583f539cdbc762e6";
    hash = "sha256-L7Uca5hJV19/WHYG+MkFWX6BwXDInfSYsOrnZdM9ejY=";
  };

  leanInk = fetchGitPackage {
    pname = "leanInk";
    version = "doc-gen";
    owner = "hargonix";
    repo = "LeanInk";
    rev = "2447df5cc6e48eb965c3c3fba87e46d353b5e9f1";
    hash = "sha256-asHVaa1uOxpz5arCvfllIrJmMC9VDm1F+bufsu3XwN0=";
  };

  mathlib = fetchGitPackage {
    pname = "mathlib";
    version = "v4.3.0";
    owner = "leanprover-community";
    repo = "mathlib4.git";
    rev = "f04afed5ac9fea0e1355bc6f6bee2bd01f4a888d";
    hash = "sha256-B0pZ7HwJwOrEXTMMyJSzMLLyh66Bcs/CqNwC3EKZ60I=";
  };

  proofwidgets = fetchGitPackage {
    pname = "proofwidgets";
    version = "v0.0.23";
    owner = "leanprover-community";
    repo = "ProofWidgets4";
    rev = "909febc72b4f64628f8d35cd0554f8a90b6e0749";
    hash = "sha256-twXXKXXONQpfzG+YLoXYY+3kTU0F40Tsv2+SKfF2Qsc=";
  };

  std = fetchGitPackage {
    pname = "std";
    version = "v4.3.0";
    owner = "leanprover";
    repo = "std4";
    rev = "2e4a3586a8f16713f16b2d2b3af3d8e65f3af087";
    hash = "sha256-agWcsRIEJbHSjIdiA6z/HQHLZkb72ASW9SPnIM0voeo=";
  };
}
