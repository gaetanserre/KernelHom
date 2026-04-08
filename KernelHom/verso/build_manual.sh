set -x -e

lake exe cache get
lake build
rm -rf html _out
lake exe manual
mkdir html
mv _out/html-multi/* html/
rm -rf _out
mkdir -p html/static
cp static_files/* html/static