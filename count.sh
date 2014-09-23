#!/bin/bash
n_sturm=`cat Sturm.thy Sturm_Theorem.thy | wc -l`
n_method=`cat Sturm_Method.thy *.ML | wc -l`
n_analysis=`cat Lib/*Analysis*.thy | wc -l`
n_poly=`cat Lib/*Poly*.thy | wc -l`
n_total=$((n_sturm + n_method + n_analysis + n_poly))
p_sturm=$(bc <<< "scale=2; 100 * $n_sturm / $n_total")
p_method=$(bc <<< "scale=2; 100 * $n_method / $n_total")
p_analysis=$(bc <<< "scale=2; 100 * $n_analysis / $n_total")
p_poly=$(bc <<< "scale=2; 100 * $n_poly / $n_total")
echo "Sturm: $p_sturm %"
echo "Method: $p_method %"
echo "Polynomials: $p_poly %"
echo "Analysis: $p_analysis %"
