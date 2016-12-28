for f in inputs/aim*-50-*
#for f in inputs/aim*
do
    echo "About to do " $f
    time ./dpll_with_watched < $f
    #./dpll_with_watched < $f
done
