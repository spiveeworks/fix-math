#!/bin/sh
tcc -run approx.c
for i in *.ppg
do
    convert "$i" "$i.png"
done
sxiv *.png
