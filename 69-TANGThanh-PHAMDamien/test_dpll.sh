#!/bin/bash

# Function to test a file
test_file() {
    local file=$1
    local expected_result=$2
    
    local filename=$(basename "$file")
    if [ "$filename" == "bf1355-075.cnf" ]; then
        echo "Skipping $filename"
        return 0
    fi

    echo "Testing file: $file"
    make clean
    make
    result=$(./dpll "$file" | head -n 1 | awk '{print $1}')
    echo "Expected result for $file: $expected_result"
    echo "Obtained result for $file: $result"
    echo

    if [ "$expected_result" == "$result" ]; then
        if [ "$result" == "SAT" ]; then
            ((sat_counter++))
        elif [ "$result" == "UNSAT" ]; then
            ((unsat_counter++))
        fi
        return 0
    else
        return 1
    fi
}

# Test folders
sat_folder="/home/pain/Documents/dpll-solveur/test-files/dimacs/SAT"
unsat_folder="/home/pain/Documents/dpll-solveur/test-files/dimacs/UNSAT"

# Counters
sat_counter=0
unsat_counter=0
sat_total=$(ls -1q $sat_folder | wc -l)
unsat_total=$(ls -1q $unsat_folder | wc -l)

# Test SAT files
echo "Testing SAT files:"
for file in $sat_folder/*; do
    test_file $file "SAT" || echo "Test failed for $file"
done

# Test UNSAT files
echo "Testing UNSAT files:"
for file in $unsat_folder/*; do
    test_file $file "UNSAT" || echo "Test failed for $file"
done

# Display counter results
echo "Number of SAT results obtained: $sat_counter/$sat_total"
echo "Number of UNSAT results obtained: $unsat_counter/$unsat_total"
