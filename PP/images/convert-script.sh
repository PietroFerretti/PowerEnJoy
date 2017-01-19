#! /bin/bash
for x in $( ls ); do
	pdftoppm -png -rx 300 -ry 300 $x $x
done;
