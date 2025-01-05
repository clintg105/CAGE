MakeBoxes[closedIntervalBracket[x__], fmt : TraditionalForm] ^:= 
 RowBox[{"[", RowBox[Riffle[BoxForm`ListMakeBoxes[{x}, fmt], ","]], 
   "]"}]

Format[ind[fx_, x_, {a_, b_}], TraditionalForm] := 
 Subscript[\[Delta], x \[Element] closedIntervalBracket[a, b]][fx]
Format[ind[x_, x_, {a_, b_}], TraditionalForm] := 
 Subscript[\[Delta], closedIntervalBracket[a, b]][x]

 ind[\[Lambda]_. * fz_ + \[Delta]_., z_Symbol, {a_, b_}] /;
  ! And[\[Lambda] === 1, \[Delta] === 0] && ! FreeQ[fz, z] :=
 ind[fz, z, {( a - \[Delta])/\[Lambda], ( b - \[Delta])/\[Lambda]}]

SetAttributes[ind, HoldFirst](* this is only so g can be Sqrt *)
ind[g_[fz_], z_Symbol, {a_, b_}] /;
  ! FreeQ[fz, z] &&
   (If[FunctionInjective[g[fz], z, PerformanceGoal -> "Speed"] === 
      True, True,
     FunctionInjective[{g[fz], a < z < b}, z, 
      PerformanceGoal -> "Speed"]]) :=
 Module[{gi = InverseFunction[g[#] &], bnds, fm},
  (* TODO: Faster methods in other (not purely symbolic) cases *)
  fm = FunctionMonotonicity[g[z], z, PerformanceGoal -> "Speed"];
  If[SameQ[Head@fm, ConditionalExpression],
   fm = fm[[1]]];(* TODO: Context tracking *)
  Switch[fm,
   1, ind[fz, z, {gi[a], gi[b]}],
   0, {Indeterminate, "ind with constant mapping"},
   -1, ind[fz, z, {gi[b], gi[a]}],
   Indeterminate, bnds = {gi[b], gi[a]}; 
   ind[fz, z, {Min @@ bnds, Max @@ bnds}]
   ]
  ]