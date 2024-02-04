#!/bin/sh
tcc -run approx.c
for i in *.ppm
do
    convert "$i" "$i.png"
done
sxiv *.png
