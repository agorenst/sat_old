for f in inputs/aim*-200*
#for f in inputs/aim*-50*
#for f in inputs/aim*
do
    echo $f
    ./sat < $f
done
