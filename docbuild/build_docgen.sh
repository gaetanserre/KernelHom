set -x -e

MATHLIB_NO_CACHE_ON_UPDATE=1 lake update doc-gen4
lake build KernelHom:docs

cp -r .lake/build/doc ../html/