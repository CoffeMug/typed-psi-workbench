#!/bin/bash

HOME=`dirname $0`
INSTANCEFILE="$1"
STRUCTNAME="$2"
shift
shift

if [ "$1" == "-i" ]; then
    echo "Psi-calculi workbench 2011, Copyright (C) 2011 Ramunas Gutkovas";
    echo "Psi-calculi comes with ABSOLUTELY NO WARRANTY; for details";
    echo "type 'warranty;'. This is free software, and you are welcome";
    echo "to redistribute it under certain conditions; type 'copyright;'";
    echo "for details.";
fi


(cat <<END
PolyML.print_depth(~1);

val dir = OS.FileSys.getDir ();
OS.FileSys.chDir "$HOME/../src";
use "ROOT.ML";
OS.FileSys.chDir dir;

use "$INSTANCEFILE";
print "\n\nPsi-calculi Workbench 2011 for $STRUCTNAME\n\n\n";
${STRUCTNAME}.start();
END

[ "$1" == "-i" ] && cat
) | /home/eaminkh/polyml/polyml.5.5.2/poly -q

