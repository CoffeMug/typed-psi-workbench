#!/bin/bash

PROGRAM=$1

[ -z "$PROGRAM" ] && echo "Please provide a program name" && exit 1

(cat <<END
PolyML.print_depth(0);
use "$PROGRAM.ML";
PolyML.export ("$PROGRAM", start);
END
) | poly -q && gcc -o "$PROGRAM" "$PROGRAM.o" -lpolyml -lpolymain && rm -f "$PROGRAM.o"

