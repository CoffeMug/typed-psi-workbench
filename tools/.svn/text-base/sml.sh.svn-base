#!/bin/sh

if [ -z "$SMLBIN" ]; then
    SML=poly
else
    SML="$SMLBIN"
fi

which "$SML" || {
    echo "The SML executable '$SML' is not on the path!"
    exit 1
}

if [ -z "$PSI_WORKBENCH_HOME" ]; then
    SML_SH_DIR=`dirname "$0"`
    PSI_WORKBENCH_HOME="$SML_SH_DIR/.."
fi

sml_interactive=yes
if [ "$1" = '-n' ]; then
    sml_interactive=no
    shift
fi

(cat <<END
PolyML.print_depth 0;
structure PsiWorkBencHome = struct val home = "$PSI_WORKBENCH_HOME/" end;
use "$PSI_WORKBENCH_HOME/src/missing.ML";
use "$PSI_WORKBENCH_HOME/src/parser.ML";
use "$PSI_WORKBENCH_HOME/tools/uses.ML";
PolyML.print_depth 1;
val uses = Uses.uses;
END

for f in "$@"; do echo "uses \"$f\";"; done;

echo "PolyML.print_depth 100;"

[ $sml_interactive = yes ] && cat
) | $SML

