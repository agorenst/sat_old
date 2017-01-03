for f in inputs/aim*
#for f in inputs/aim*
do
    echo "About to do " $f
    time ./sat < $f
done
