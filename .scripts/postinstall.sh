#!/bin/bash
set -euxo pipefail

# if bun-webkit node_modules directory exists
if [ -d ./node_modules/bun-webkit ]; then
    rm -f bun-webkit
    # get the first matching bun-webkit-* directory name
    ln -s ./node_modules/$(ls ./node_modules | grep bun-webkit- | head -n 1) ./bun-webkit
fi
