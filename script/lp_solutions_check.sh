files=${$1:"test/solver/mps/*.mps"}

# for each file in the test/solver/mps directory
# run the lp_solve command
# if the command fails, print FAIL
for file in $files; do
    echo "Running lp_solve on $file"
    lp_solve -fmps "$file" -noint > /dev/null
    error_code=$?
    # Remove any "* @set-info :status" line
    sed -i '/\* @set-info :status/d' $file
    if [ $error_code -eq 2 ]; then
        echo "lp_solve $file: INFEAS"
        echo -e "* @set-info :status unsat\n$(cat $file)" > $file
    elif [ $error_code -ne 0 ]; then
        echo "lp_solve $file: FAIL with error code $error_code"
        exit 1
    else
        echo "lp_solve $file: OK"
        echo -e "* @set-info :status sat\n$(cat $file)" > $file
    fi
done
