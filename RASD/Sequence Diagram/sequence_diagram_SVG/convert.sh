#!/bin/bash
for var in "$@"
do
	s=${var##*/}
	base=${s%.svg}
	echo 'converting' $var
	inkscape -D -z --file=$var --export-pdf=$base.pdf --export-latex
	echo 'done!'
	echo '*****'
done
