#!/bin/bash
n_sturm=`cat Sturm.thy Sturm_Library.thy | wc -l`
n_method=`cat Sturm_Method.thy | wc -l`
n_analysis=`cat *Analysis*.thy | wc -l`
n_poly=`cat *Poly*.thy | wc -l`
n_misc=`cat List_Group.thy Misc.thy | wc -l`
n_total=$((n_sturm + n_method + n_analysis + n_poly + n_misc))
p_sturm=$(bc <<< "scale=2; 100 * $n_sturm / $n_total")
p_method=$(bc <<< "scale=2; 100 * $n_method / $n_total")
p_analysis=$(bc <<< "scale=2; 100 * $n_analysis / $n_total")
p_poly=$(bc <<< "scale=2; 100 * $n_poly / $n_total")
p_misc=$(bc <<< "scale=2; 100 * $n_misc / $n_total")
echo "Sturm: $p_sturm %"
echo "Method: $p_method %"
echo "Polynomials: $p_poly %"
echo "Analysis: $p_analysis %"
echo "Miscellaneous: $p_misc %"
