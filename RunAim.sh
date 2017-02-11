#for f in inputs/ssa*
#for f in inputs/aim*-200*
#for f in inputs/aim*-50*
for f in inputs/aim*no*
#for f in inputs/aim*yes*
#for f in inputs/aim*-100*
#for f in inputs/uf75-*
#for f in inputs/uf125-*
#for f in inputs/fla*35*
do
    #echo $f
    ./sat < $f
done
echo "yes"
for f in inputs/aim*yes*
do
    #echo $f
    ./sat < $f
done
