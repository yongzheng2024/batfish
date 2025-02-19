#!/bin/bash

for file in *; do
if [ -f "$file" ]; then
python3 smt2_format.py "$file"
fi
done
