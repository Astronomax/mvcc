#!/bin/bash

BINARY="./debug-build/stress"
LOG_FILE="crash.log"
COUNTER=0

echo "Stress test started. Output will be saved to '$LOG_FILE' on crash."
echo "Press Ctrl+C to stop."

while true; do
    ((COUNTER++))
    echo -n "Run #$COUNTER... "

    OUTPUT=$($BINARY 2>&1)
    STATUS=$?
    
    if [ $STATUS -eq 0 ]; then
        echo "OK"
    else
        echo "FAILED (saving output to '$LOG_FILE')"
        echo "=== Crash on run #$COUNTER ===" > "$LOG_FILE"
        echo "Exit status: $STATUS" >> "$LOG_FILE"
        echo "=== Program output ===" >> "$LOG_FILE"
        echo "$OUTPUT" >> "$LOG_FILE"
        exit 1
    fi
done
