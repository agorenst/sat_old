for f in inputs/aim*-50*
#for f in inputs/aim*
do
    echo "About to do " $f
    ./sat < $f
done
