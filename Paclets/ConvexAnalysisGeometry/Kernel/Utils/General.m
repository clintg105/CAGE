(* ::Package:: *)

Package["ConvexAnalysisGeometry`Utils`"]

PackageExport["trep"]
PackageExport["mtrep"]

PackageExport["repelem"]
PackageExport["cyclicTakeUpTo"]

PackageExport["bsxRow"]
PackageExport["addRow"]

PackageExport["pwGetPairs"]
PackageExport["pwAddConditionIgnoreLast"]
PackageExport["pwAddCondition"]
PackageExport["pwDropLast"]

trep[expr_, vars_, inp_] := expr /. Thread[vars -> inp]
mtrep[expr_, vars_, inp_] := expr /. Thread[vars -> #] & /@ inp

repelem[ix_List] := 
 Flatten[ConstantArray[#1, #2] & @@@ Transpose@{Range[Length[ix]], ix}]
repelem[v_List, ix_List] := v[[repelem[ix]]]

cyclicTakeUpTo[v_List, n_Integer] := 
 v[[Mod[Range[n] - 1, Length[v]] + 1]]

bsxRow::usage = 
  "bsxRow[op, mat, row] performs a broadcast-style operation between \
a row vector `row` and a matrix `mat` using the listable binary operation `op`. 
`op` must be listable.
Uses transpose-based optimization for performance. See: \
https://mathematica.stackexchange.com/questions/95033/add-a-vector-to-a-list-of-vectors.
Example: bsxRow[Plus, mat, row] adds `row` to each row (element) of \
`mat`.";
bsxRow[op_, mat_, row_] := Transpose[op[row, Transpose[mat]]]
addRow[mat_, row_] := Transpose[row + Transpose[mat]]

pwGetPairs[f_Piecewise] := Module[{vals, cnds},
  vals = Append[f[[1, ;; , 1]], f[[2]]];
  cnds = f[[1, ;; , 2]];
  cnds = Append[cnds, Not@Fold[Or, cnds]];
  {vals, cnds}]
pwAddConditionIgnoreLast[f_Piecewise, cnd_] := 
  (f[[1, ;; , 2]] = # && cnd & /@ f[[1, ;; , 2]]; f)
pwAddCondition[f_Piecewise, cnd_] := Module[{vals, cnds},
  {vals, cnds} = pwGetPairs[f];
  cnds = (# && cnd &) /@ cnds;
  Piecewise[{vals, cnds}\[Transpose], Undefined[]]]

(*TODO: pwDropLastSafe *)
pwDropLast[f_Piecewise] := 
 f /. Piecewise -> \[FormalL] //. \[FormalL][a_List, b_] :> 
   Piecewise[a[[1 ;; -2]], a[[-1, 1]]]