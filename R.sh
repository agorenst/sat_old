for f in inputs/$1*
do
    #echo $f
    ./sat < $f > /dev/null
done
