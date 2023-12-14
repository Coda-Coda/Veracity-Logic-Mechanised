let pkgs = import (
  builtins.fetchTarball {
  url = "https://github.com/nixos/nixpkgs/archive/e97b3e4186bcadf0ef1b6be22b8558eab1cdeb5d.tar.gz";
  sha256 = "114ggf0xbwq16djg4qql3jljknk9xr8h7dw18ccalwqg9k1cgv0g";
}) {}; in

let
  my-python-packages = with pkgs; python-packages: with python-packages; [
    (
      buildPythonPackage rec {
        pname = "alectryon";
        version = "beta";
        src = ( pkgs.fetchFromGitHub {
                  owner  = "cpitclaudel";
                  repo   = "alectryon";
                  rev    = "11e8cdc8395d66858baa7371b6cf8e827ca38f4a";
                  sha256 = "15am9ykgqkrhwi5760mjkknkh4l8i64rvgkzwxj2gari4v2vqgjr"; } );
        doCheck = false;
        propagatedBuildInputs = [
            pygments
            dominate
            beautifulsoup4
            docutils
            sphinx
        ];

        meta = with lib; {
          homepage = "https://github.com/cpitclaudel/alectryon";
          description = "A collection of tools for writing technical documents that mix Coq code and prose";
          license = licenses.mit;
          maintainers = with maintainers; [ Zimmi48 ];
        };
      }
    )
    pygments
  ]; 
  python-with-my-packages = with pkgs; python3.withPackages my-python-packages;
in

pkgs.mkShell {
  buildInputs = with pkgs; [ 
      coq_8_14
      coqPackages_8_14.serapi
      python-with-my-packages
    ];
  shellHook = ''
    
  '';
}