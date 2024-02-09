#!/bin/sh
agda --latex lc.lagda && cd latex && xelatex lc.tex && cd ..
