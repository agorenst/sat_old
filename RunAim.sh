for f in inputs/aim*-50-*
#for f in inputs/aim*
do
    echo "About to do " $f
    #time ./sat_strong_prop < $f
    ./basic_dpll < $f
done
