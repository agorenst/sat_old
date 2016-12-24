for f in inputs/aim*-50-*
#for f in inputs/aim*
do
    echo "About to do " $f
    #time ./sat_strong_prop < $f
    ./dpll_with_watched < $f
done
