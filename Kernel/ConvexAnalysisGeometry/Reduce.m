(* ::Package:: *)

Package["ConvexAnalysisGeometry`"]

PackageExport["cvxReduce"] (* Note: not crawler*)
PackageExport["cvxResolveOverReals"]

cvxReduce::usage = "cvxReduce[x_] reduces all symbolic convex \
functions in `x` to standard symbolic form"
cvxReduceCrawler[f_[a___]] := f @@ (cvxReduce /@ {a})
cvxReduceCrawler[a_Symbol] := a
cvxReduceCrawler[a_?NumberQ] := a
cvxReduceCrawler[indicator[cnd_]] := Piecewise[{{0, cnd}}, Infinity]
cvxReduce[x_] := cvxReduceCrawler[x] // PiecewiseExpand


cvxResolveOverReals::usage = "cvxResolveOverReals[x_] simplifies \
expressions over R using techniques often missed by mathematica"
cvxResolveOverReals[f_[a___], s___] := 
 f @@ (cvxResolveOverReals[#, s] & /@ {a})
cvxResolveOverReals[a_Symbol, ___] := a
cvxResolveOverReals[a_?NumberQ, ___] := a
(* level set of 1 anyway, common case mathematica misses *)
cvxResolveOverReals[Power[expr_, 1/2] <= 1, vars_, cnd_] := If[
  Simplify[expr >= 0, cnd] === True || 
   FullSimplify[
     Reduce[expr >= 0 && Im[Alternatives @@ vars] == 0, Complexes], 
     cnd] === True,
  cvxResolveOverReals[expr, vars, cnd] <= 1, 
  Power[cvxResolveOverReals[expr, vars, cnd], 1/2] <= 1
  ]
cvxResolveOverReals[a_ + indicator[b_], vars_, cnd_] := 
 cvxResolveOverReals[a, vars, cnd && b] + indicator[b]

cvxResolveOverReals[Max[a_, b_], vars_, cnd_] := Which[
  FullSimplify[
    Reduce[a >= b && Im[Alternatives @@ vars] == 0, Complexes], cnd
    ] === True,
  a,
  FullSimplify[
    Reduce[a <= b && Im[Alternatives @@ vars] == 0, Complexes], cnd
    ] === True,
  b,
  True,
  Max @@ (cvxResolveOverReals[#, vars, cnd] & /@ {a, b})
  ]
cvxResolveOverReals[Min[a_, b_], vars_, cnd_] := Which[
  FullSimplify[
    Reduce[a <= b && Im[Alternatives @@ vars] == 0, Complexes], cnd
    ] === True,
  a,
  FullSimplify[
    Reduce[a >= b && Im[Alternatives @@ vars] == 0, Complexes], cnd
    ] === True,
  b,
  True,
  Max @@ (cvxResolveOverReals[#, vars, cnd] & /@ {a, b})
  ]
(*This old way breaks:
f=initializeSet[{x,y}.{x,y}<=1/.Thread[{x,y}->{x,y}+1],{x,y}];
f["polar"]["polar"]*)