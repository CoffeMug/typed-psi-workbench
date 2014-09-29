#!/bin/sh

if [ -z "$PSI_WORKBENCH_HOME" ]; then
    SML_SH_DIR=`dirname "$0"`
    PSI_WORKBENCH_HOME="$SML_SH_DIR/.."
fi

(cat <<END
print (Uses.prUses "src/workbench");
END
) | $PSI_WORKBENCH_HOME/tools/sml.sh

