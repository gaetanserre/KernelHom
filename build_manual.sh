set -x -e

rm -rf _out html
lake exe manual
mkdir html
mv _out/html-multi/* html/
rm -rf _out
mkdir -p html/static
cp KernelHom/verso/static_files/* html/static