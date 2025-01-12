(* ::Package:: *)

(* ::Input::Initialization:: *)
Package["ConvexAnalysisGeometry`"]
PackageImport["ConvexAnalysisGeometry`Utils`"]


(* ::Section::Closed:: *)
(*Geometry*)


(* ::Input::Initialization:: *)
PackageExport["AffineHullDim"]


(* ::Input::Initialization:: *)
AffineHullDim::usage = "AffineHullDim[pts_List] returns the \
dimension of the affine hull spanned by `pts`"
(* The rank of the (centered) point matrix is the dimension of the \
  affine subspace spanned by the points*)
AffineHullDim[pts_List] := MatrixRank[addRow[pts[[2 ;;]], -pts[[1]]]]


(* ::Section::Closed:: *)
(*Reduction*)


(* ::Input::Initialization:: *)
PackageExport["cvxReduce"] (* Note: not crawler*)
PackageExport["cvxResolveOverReals"]


(* ::Input::Initialization:: *)
cvxReduce::usage = "cvxReduce[x_] reduces all symbolic convex \
functions in `x` to standard symbolic form"
cvxReduceCrawler[f_[a___]] := f @@ (cvxReduce /@ {a})
cvxReduceCrawler[a_Symbol] := a
cvxReduceCrawler[a_?NumberQ] := a
cvxReduceCrawler[indicator[cnd_]] := Piecewise[{{0, cnd}}, Infinity]
cvxReduce[x_] := cvxReduceCrawler[x] // PiecewiseExpand


(* ::Input::Initialization:: *)
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
  f = initializeSet[{x, y}.{x, y} <= 1 /. Thread[{x, y} -> {x, y} + 1], {x, y}];
  f["polar"]["polar"]*)


(* ::Section:: *)
(*Functions*)


(* ::Section::Closed:: *)
(*Unsorted1124*)


(* ::Package:: *)
(**)


(* ::Input::Initialization:: *)
Package["ConvexAnalysisGeometry`"]
PackageImport["ConvexAnalysisGeometry`Utils`"]

PackageExport["formalVector"]
PackageExport["formalParameter"]
PackageExport["zeroSymmetric"]
PackageExport["bounded"]
PackageExport["polar"]
PackageExport["recc"]
PackageExport["polarRecc"]
PackageExport["support"]
PackageExport["convex"]
PackageExport["positiveHomogeneous"]
PackageExport["sublinear"]
PackageExport["epi"]
PackageExport["dom"]
PackageExport["lev"]
PackageExport["subgradient"]
PackageExport["subgradientPiecewiseMultiValued"]
PackageExport["c1SubgradientR1"]
PackageExport["toRegion"]
PackageExport["solvePiecewise"]
PackageExport["toInequality"]

PackageExport["varUsageOrdering"]
PackageExport["sortedSubsetIndices"]

PackageExport["reduceParametricPiece"]
PackageExport["plotParamPiece"]

PackageExport["piecewiseNestedQ"]
PackageExport["piecewiseValueWrapper"]
PackageExport["mapPiecewiseValues"]
PackageExport["nestedPiecewiseFromHierarchicalLogic"]

PackageExport["int"]
PackageExport["originRegion"]
PackageExport["orthCompAff"]
PackageExport["ray"]

PackageExport["lagrangeStationaryPoints"]
PackageExport["toLevelRegion"]
PackageExport["conicHull2"]
PackageExport["conicHull"]

PackageExport["polarParameterization"]
PackageExport["boundaryAtlas"]
PackageExport["boundaryAtlasLookup"]
PackageExport["boundaryAtlasPlot"]
PackageExport["boundaryAtlasPolarParamsReduced"]

(* opt class stuff *)
PackageExport["freeOptQ"]
PackageExport["optCases"]
PackageExport["objRelationGraph"]
PackageExport["functionList"]

PackageExport["optObj"]
PackageExport["optID"]
PackageExport["isComputed"]
PackageExport["nVars"]
PackageExport["sub"]

PackageExport["plotBoundsParser"]
PackageExport["plot"] (* overloaded for all *)
PackageExport["cplot"] (* overloaded for all *)

PackageExport["optFun"]

PackageExport["optMaxFun"]

PackageExport["optSet"]

PackageExport["optIntSet"]
PackageExport["project"]

PackageExport["optISet"]

PackageExport["optSet"]

PackageExport["setOptFormat"]

PackageExport["simpleSupport"]

(* users should avoid custom specifcation of \[FormalX], \[FormalS], \
  and \[FormalZeta] do to use in codebase (as well as \[FormalL], due \
    to use as generic symbol)*)
formalScalar = \[FormalX];

formalVector[n_Integer] := Array[Subscript[formalScalar, #] &, n]
formalVector[n_Integer, m_] := 
  Array[Superscript[Subscript[formalScalar, #], m] &, n]
formalVector[n_List, varargin___] := 
  With[{x = formalVector[Length[n], varargin]}, 
    If[SameQ[n, x], x /. formalScalar -> \[FormalY], x]]

formalVectors[n_, m_] := formalVector[n, #] & /@ Range[m]

formalParameter[varargin___] := 
  formalVector[varargin] /. formalScalar -> \[FormalS]
formalCovector[varargin___] := 
  formalVector[varargin] /. formalScalar -> \[FormalZeta]

zeroSymmetric[cons_LessEqual, vars_] := Reduce[ForAll[vars, 
    Implies[cons, trep[cons, vars, -vars]]], 
  vars, Reals]
bounded[cons_, vars_] := 
  Resolve[Exists[\[FormalL], 
      ForAll[Evaluate[vars], cons, vars . vars <= \[FormalL]]]]

polar[expr_, vars_] := Module[{newVars = formalCovector[vars], pCnd}, 
  pCnd = ForAll[Evaluate[newVars], trep[expr, vars, newVars], 
    vars . newVars <= 1];
  {Reduce[pCnd, newVars, Reals], vars}]

recc[expr_, vars_] := Module[{newVars = formalCovector[vars], reccCnd}, 
  reccCnd = 
  ForAll[Evaluate[newVars], trep[expr, vars, newVars], 
    trep[expr, vars, newVars + vars]];
  {Reduce[reccCnd, newVars, Reals], vars}]
polarRecc[expr_, vars_] := polar @@ recc[expr, vars]

support[expr_, vars_] := With[{newVars = formalVector[vars]}, 
  Maximize[{vars . newVars, trep[expr, vars, newVars]}, newVars, 
    Reals][[1]]
]

convex[expr_, vars_] := 
  Module[{x = formalVectors[vars, 2], c = {\[FormalL], 1 - \[FormalL]}}, 
    (* this is amlos never used in favor of FunctionComplexity *)
    Reduce[ForAll[Evaluate[Append[vars, \[FormalL]]], 0 < \[FormalL] < 1, 
        trep[expr, vars, c . x] <= c . mtrep[expr, vars, x]], 
      vars, Reals]
  ]
positiveHomogeneous[expr_, vars_] := 
  Reduce[ForAll[Evaluate[Append[vars, \[FormalL]]], \[FormalL] > 0, 
      \[FormalL] expr == trep[expr, vars, \[FormalL] vars]], 
    vars, Reals]
(* sublinear - Great example: when working with classes, dfn 3.3.1 or \
  prop 3.3.2 can be used *)
sublinear[expr_, vars_] := 
  Module[{x = formalVectors[vars, 2], l = formalParameter[2]}, 
    Reduce[ForAll[Evaluate[Flatten[Join[x, l]]], Fold[And, # > 0 & /@ l], 
        trep[expr, vars, l . x] == l . mtrep[expr, vars, x]], 
      vars, Reals]
  ]

epi[expr_, vars_] := 
  With[{x = 
      formalVector[Length[vars] + 1]}, {trep[expr, vars, x[[;; -2]]] <= 
      x[[-1]], x}]
(*lev[expr_, vars_, alpha_:1] := {expr <= alpha, vars}
  dom[expr_, vars_] := {expr<Infinity, vars}*)

dom[Plus[expr_, indicator[cnd_]], vars_] := dom[{expr, cnd}, vars]
dom[{Plus[expr_, indicator[cnd_]], cnd0_}, vars_] := 
  dom[{expr, cnd && cnd0}, vars]

dom[expr_, vars_] := dom[{expr, True}, vars]
dom[{expr_, cnd_}, 
  vars_] := {Reduce[expr < Infinity && cnd, vars, Reals], vars}

lev[expr_, vars_, alpha_ : 1] := 
  lev[{expr /. indicator[_] -> 0, dom[expr, vars][[1]]}, vars, alpha]
lev[{expr_, cnd_}, vars_, 
  alpha_ : 1] := {expr <= alpha && cnd && dom[expr, vars][[1]], vars}

(*cvxReduce[{expr_, True}] := expr
  cvxReduce[expr_:Except[_List]] := cvxReduce[{expr, True}]
  cvxReduce[expr_Plus] := cvxReduce[{expr, True}]
  cvxReduce[{expr_, cnd_}] := Piecewise[{{cvxReduce[expr], cnd}}, \
    Indeterminate]
  cvxReduce[{Plus[expr_, indicator[cndi_]], cnd_}] := Piecewise[{{cvxReduce[\
          expr], cndi && cnd//Reduce}, {Infinity, !cndi && cnd//Reduce}}, Indeterminate]
  cvxReduce[Plus[expr_, indicator[cndi_]]] := Piecewise[{{cvxReduce[expr], \
        cndi}}, Infinity]
  cvxReduce[LessEqual[a_, b_]] := LessEqual[cvxReduce[a], cvxReduce[b]]*)

subgradient[expr_, vars_] := 
  Module[{x = vars, y = formalVector[vars], z = formalCovector[vars]}, 
    Reduce[ForAll[y, 
        (y - x) . z <= trep[expr, vars, y] - trep[expr, vars, x]], 
      z, Reals]
  ]

subgradientPiecewiseMultiValued[expr_, vars_] := 
  With[{pVars = formalCovector[vars], sg = subgradient[expr, vars]}, 
    mapPiecewiseValues[Switch[#, 
        _Integer, #, (* catches Piecewise default zero case *)
        _Equal, 
        With[{f = Flatten[pVars /. {ToRules[#]}]}, 
          If[Length[f] == 1, f[[1]], ImplicitRegion[#, Evaluate[pVars]]]], 
        _, ImplicitRegion[#, Evaluate[pVars]]
      ] &, nestedPiecewiseFromHierarchicalLogic[sg, pVars]]]

c1SubgradientR1[f_, {var_}] := Module[{deriv, disc, points}, 
  (* does not check jump discontinuities! *)
  (* Convex 1-var *)
  deriv = D[f, var];
  (*Find the points of discontinuity*)
  disc = FunctionDiscontinuities[deriv, var];
  (*Find the actual points where discontinuity occurs*)
  points = SolveValues[disc, var];
  (*Glue the derivative together at points of discontinuity*)
  PiecewiseExpand @ Piecewise[
    (*For each point of discontinuity, form an interval*)
    Append[{
        Interval[{
            Limit[deriv, var -> #, Direction -> "FromAbove"], 
            Limit[deriv, var -> #, Direction -> "FromBelow"]
        }], 
        var == #
      } & /@ points, 
      (*For other points, simply use the derivative*)
      {deriv, True}]
  ]
]

toRegion[f_] := Module[{f0 = f, ir}, 
  (* Reduces pwmv function with 'Interval' and dervied \
    ImplicitRegions to one with just ImplicitRegions. *)
  (* Do reduction of ImplicitRegion *)
  f0 = f0 /. ImplicitRegion -> ir;
  f0 = f0 //. {
    Interval[{a_, b_}] :> ir[a <= y <= b, {y}], 
    ir[fxy_, {y_}] + fx_ :> ir[fxy /. y -> y - fx, {y}]
  };
  f0 = f0 /. ir -> ImplicitRegion;
  (* Return reduced function *)
  f0
];
solvePiecewise[eq_, var_] := Module[
  {lhs, rhs, rel, pieces, regionPieces, nonRegionPieces, 
    regionSolutions, nonRegionSolutions, solutions}, 
  (*TODO: Fix lhs needing to be equation *)
  (*Get left hand side and right hand side of the equation*)
  If[Head[eq] === Equal, 
    {lhs, rhs} = List @@ eq;
    rel = Equal, 
    lhs = eq[[1]];
    rhs = eq[[2]];
    rel = Head[eq]];
  lhs = toRegion[lhs];
  (*Get piecewise pieces*)
  pieces = Transpose @ pwGetPairs[lhs];
  (*Separate region pieces and non-region pieces*)
  regionPieces = Select[pieces, Head[#[[1]]] === ImplicitRegion &];
  nonRegionPieces = Select[pieces, Head[#[[1]]] =!= ImplicitRegion &];
  (*Process each region piece*)
  regionSolutions = (r |-> Element[rhs, r[[1]]] && r[[2]]) /@ 
  regionPieces;
  (*Echo[regionPieces//MatrixForm];*)
  (*Echo[{regionPieces, Reduce[Or @@ regionSolutions, var, Reals], 
        ImplicitRegion[Reduce[Or @@ regionSolutions, var, Reals], var]}];*)
  (*Process each non-region piece*)
  nonRegionSolutions = (expr |-> rel[expr[[1]], rhs] && expr[[2]]) /@ 
  nonRegionPieces;
  (*Echo[Reduce[Or @@ nonRegionSolutions, var, Reals]];*)
  (*Join all solutions*)
  solutions = Join[regionSolutions, nonRegionSolutions];
  (*Create final implicit region*)
  ImplicitRegion[Reduce[Or @@ solutions, var, Reals], var]]

toInequality[p_] := p /. {
  Less[a_, b_, c_] :> Inequality[a, Less, b, Less, c], 
  LessEqual[a_, b_, c_] :> Inequality[a, LessEqual, b, LessEqual, c], 
  (* assuming the variable of interest is always on the left (based \
      on reduce) *)
  Less[a_, b_] :> Inequality[-Infinity, Less, a, Less, b], 
  LessEqual[a_, b_] :> Inequality[-Infinity, Less, a, LessEqual, b], 
  Greater[a_, b_] :> Inequality[b, LessEqual, a, Less, Infinity], 
  GreaterEqual[a_, b_] :> Inequality[b, Less, a, Less, Infinity]};
toInequalityLeftBiasedToCenter = toInequality;

(* for ordering generation for-loops, like in ParametricPlot *)
varUsageOrdering[exprs_, vars_] := 
  OrderingBy[Transpose[{vars, exprs}], ! FreeQ[#[[2]], #[[1]]] &]

sortedSubsetIndices[subset_, superset_] := With[
  (* things not in superset go at end *)
  {orderInBigList = 
    Flatten[Position[superset, #] & /@ subset /. {} -> Infinity]}, 
  Ordering[orderInBigList, All, LessEqual]
]

reduceParametricPiece[p_, vars_ : {}] := 
  Module[{(*pSplit, pHeads, eqIxs, mixedInEqIxs, constIxs, pOut*)}, 
    (* reduce each parametric peice into a list: {{f[x], g[y], h[z]}, {x, 
          y}, {{x0, x1}, {y0, y1}}}, 
      that is, {[Parametric Equations], [Parametric Variables], \
        [Parametric Bounds]}*)
    pSplit = p /. And -> List // toInequality;
    pHeads = Head /@ pSplit;
    eqIxs = Flatten @ Position[pHeads, Equal];
    mixedInEqIxs = Flatten @ Position[pHeads, Inequality];
    Assert[Length[Join[eqIxs, mixedInEqIxs]] == Length[p]];
    If[Length[mixedInEqIxs] == 0, 
      pOut = {First[vars //. {ToRules[p]}], {}, {}}, 
      pOut = {If[eqIxs === {}, vars, 
          First[vars //. {ToRules[Fold[And, pSplit[[eqIxs]]]]}]], 
        pSplit[[mixedInEqIxs]][[;; , 3]], 
        Transpose @ {pSplit[[mixedInEqIxs]][[;; , 1]], 
          pSplit[[mixedInEqIxs]][[;; , 5]]}};
    ];
    constIxs = 
    Flatten @ Position[MemberQ[pOut[[2]], #] & /@ vars, False, 1];
    pOut[[1]] = 
    pOut[[1]] /. Thread[vars[[constIxs]] -> pOut[[1]][[constIxs]]];
    (*pOut[[3]] = pOut[[3]] /. Thread[vars[[constIxs]] -> 
        pOut[[1]][[constIxs]]];*)
    pOut
  ]
reduceParametricPieces[p_, vars_] := 
  If[Head[p] === Or, 
    reduceParametricPiece[#, vars] & /@ 
    List @@ p, {reduceParametricPiece[p, vars]}]

plotParamPiece[p_, vars_, varagin___] := 
  Module[{constIxs, ordering}, If[Length[p[[1]]] == 2, 
      If[p[[2]] === {}, 
        Graphics[Point[p[[1]]]], 
        constIxs = 
        Flatten @ Position[MemberQ[p[[2]], #] & /@ vars, False, 1];
        ordering = varUsageOrdering[p[[3]], p[[2]]];
        ParametricPlot[
          p[[1]] /. Thread[vars[[constIxs]] -> p[[1]][[constIxs]]], 
          Evaluate[
            Sequence @@ ((Transpose @ 
                Join[{p[[2]][[ordering]]}, 
                  Transpose @ p[[3]][[ordering]]]) /. {{x_, -Infinity, 
                  b_} :> {x, (b - 1), b}, {x_, b_, Infinity} :> {x, 
                  b, (b + 1)}})], varagin]
      ], 
      If[p[[2]] === {}, 
        Graphics3D[Point[p[[1]]]], 
        constIxs = 
        Flatten @ Position[MemberQ[p[[2]], #] & /@ vars, False, 1];
        ordering = varUsageOrdering[p[[3]], p[[2]]];
        ParametricPlot3D[
          p[[1]] /. Thread[vars[[constIxs]] -> p[[1]][[constIxs]]], 
          Evaluate[
            Sequence @@ ((Transpose @ 
                Join[{p[[2]][[ordering]]}, 
                  Transpose @ (p[[3]][[ordering]] // N //
                    Re)]) /. {{x_, -Infinity, b_} :> {x, (b - 1), b}, {x_, 
                  b_, Infinity} :> {x, b, (b + 1)}})], varagin]
      ]
  ]]

piecewiseNestedQ[expr_] := Length[Position[expr, Piecewise]] > 1
piecewiseValueWrapper[expr_Piecewise] := 
  Piecewise[{piecewiseValueWrapper[#1], #2} & @@@ #1, 
    piecewiseValueWrapper[#2]] & @@ expr
mapPiecewiseValues[fun_, expr_] := 
  piecewiseValueWrapper[expr] /. piecewiseValueWrapper -> fun

nestedPiecewiseFromHierarchicalLogic[expr_, pVars_] := 
  Block[{exprPairedCndVal}, 
    (* Assumes expr is "Tree-Like" with pVars at the lowest level.
      Example:
      nestedPiecewiseFromHierarchicalLogic[
        (x >= 0 && ((y >= 0 && (z == x)) || (y<0 && (z == y)))) || (x<0 && (x<z<y)), 
        z] *)
    (* pVars are parametric vars, 
      these are the the variables that are NOT part of the Piecewise \
      conditions *)
    exprPairedCndVal = 
    expr //. 
    And[cnd_?(FreeQ[#, Alternatives @@ pVars] &), val_] :> {val, cnd};
    (* there is some porperty of the operator Or that makes it have to \
      be spoofed (or else it stays persistent as Head) *)
    exprPairedCndVal /. Or -> \[FormalL] //. \[FormalL][x___List] :> 
      Piecewise[{x}] /. \[FormalL] -> Or
  ]

int[R_] := RegionDifference[R, RegionBoundary[R]]
originRegion[n_] := ImplicitRegion[x == Table[0, n], x]

orthCompAff[AffineSpace[points_List]] := Module[
  (* The complement returned here will intersect the AffineSpace at \
    the first point provided in it's definition.
    Not sure of rigor here...
    
    Issues:
    This definition is "numeric" over the points due to the usage of \
    Select and Orthogonalize.*)
  {R = AffineSpace[points], p0 = points[[1]], pCen, pCenOrth}, 
  pCen = Table[p - p0, {p, points}];
  pCenOrth = 
  Select[Orthogonalize[
      pCen~Join~IdentityMatrix[RegionEmbeddingDimension[R]]], 
    Norm[#] > 0 &][[Length[points] ;;]];
  AffineSpace[{p0}~Join~Table[p + p0, {p, pCenOrth}]]
]
orthCompAff[AffineSpace[points_List], center_] := TransformedRegion[
  orthCompAff[AffineSpace[points]], 
  TranslationTransform[-points[[1]] + center]]

ray[origin_, direction_] := ConicHullRegion[{origin}, {direction}]

(* find solutions to Subscript[inf, cons] expr if exper is convex *)
lagrangeStationaryPoints[expr_, cons_Equal, vars_List] := 
  expr /. Solve[
    Eliminate[
      D[expr - \[Lambda] (cons[[2]] - cons[[1]]), {Join[
            vars, {\[Lambda]}]}] == 0, \[Lambda]], vars]

toLevelRegion[ImplicitRegion[expr_LessEqual, vars_]] := 
  levelRegion[expr[[1]] - expr[[2]] + 1, vars]
(* implicit regions don't get wrapped until later, when we are going \
  class mode *)

conicHull2[expr_, vars_] := 
  Module[{dim = Length[vars], g = Grad[expr[[1]], vars]}, 
    (* slightly fancy version *)
    (* assumes convexity *)
    If[dim == 2, 
      ConicHullRegion[{{0, 0}}, 
        SolveValues[vars . g == 0 && (expr /. LessEqual -> Equal), vars]], 
      ImplicitRegion[Reduce[vars . g == 0 && expr, vars, Reals], vars]
    ]
  ]

conicHull[expr_, vars_] := 
  Module[{dim = Length[vars], g = Grad[expr[[1]], vars]}, 
    (* assumes convexity *)
    {Reduce[vars . g == 0 && expr, vars, Reals], vars}
  ]

polarParameterization[param_, vars_] := 
  Module[{n = Length[param], grad = Transpose[Grad[param, vars]], 
      e, M}, 
    M = Transpose[{
        Array[Subscript[e, #] &, n + 1], 
        param~Join~{1}, 
        Sequence @@ Join[
          Array[grad[[##]] &, {n - 1, n}], 
          ConstantArray[{0}, n - 1]
          , 2]
    }];
    Coefficient[SolveValues[Det[M] == 0, Subscript[e, n + 1]][[1]], 
      Evaluate[Array[Subscript[e, #] &, n]]] // FullSimplify
  ]

boundaryAtlas[cnd_, vars_] := 
  Module[{cndList, allIxs, intList, bdryList, cndIxParamTuples, 
      bdrySubsetIxs, lowerCndsSimple, lowerCnds}, 
    cndList = cnd /. And -> List;
    (* only one region check: *)
    If[Not[Head[cndList] === List], cndList = {cndList}];
    allIxs = Range[Length[cndList]];
    
    intList = cndList /. LessEqual -> Less;
    bdryList = cndList /. LessEqual -> Equal;
    cndIxParamTuples = Table[
      bdrySubsetIxs = Subsets[allIxs, {ii}];
      lowerCndsSimple = 
      Fold[And, bdryList[[#]]] && 
        Fold[And, intList[[Complement[allIxs, #]]]] & /@ bdrySubsetIxs;
      lowerCndsSimple = lowerCndsSimple /. Fold[And, {}] -> True;
      lowerCnds = 
      BooleanConvert[Reduce[#, Evaluate[vars], Reals], "SOP"] & /@ 
      lowerCndsSimple;
      (If[#2 === False, Undefined, 
          With[{red = reduceParametricPieces[#2, vars]}, 
            
            If[red === {}, 
              Undefined, {#3, #1, If[Head @ #2 === Or, List @@ #2, {#2}], 
                red}]
          ]
        ]) & @@@ 
      Transpose @ {lowerCndsSimple, lowerCnds, bdrySubsetIxs} /. 
      Undefined -> Sequence[]
      , {ii, Range[1, Length[allIxs]]}];
    (* will contain {} when a boundary intersection is not on the \
      boundary of the intersecting set: *)
    cndIxParamTuples = Flatten[cndIxParamTuples, 1]
    (* cndIxParamTuples = List of tuples {{regionIxs, simpleCnd, 
          paramsLogical, paramsReduced}, ...}*)
  ]
atlasCol = 
AssociationThread[{"regionIxs", "simpleCnd", "paramsLogical", 
    "paramsReduced"} -> Range[4]];

boundaryAtlasLookup[boundaryAtlas_, vars_, testPoint_] := 
  Module[{subsetIx, paramIx, paramVals}, 
    subsetIx = 
    LengthWhile[
      boundaryAtlas[[;; , atlasCol["simpleCnd"]]], !
      trep[#, vars, testPoint] &] + 1;
    Assert[subsetIx <= Length[boundaryAtlas]](* Not a boundary point *);
    paramIx = 
    LengthWhile[
      boundaryAtlas[[subsetIx, atlasCol["paramsLogical"]]], !
      trep[#, vars, testPoint] &] + 1;
    Assert[paramIx <= Length[boundaryAtlas]](*
      Could not find suitable param? Should not happen ... *);
    paramVals = 
    trep[boundaryAtlas[[subsetIx, 
          atlasCol["paramsReduced"]]][[paramIx]][[2]], vars, testPoint];
    {subsetIx, paramIx, paramVals}
  ]

boundaryAtlasPlot[atlas_, vars_] := 
  Module[{params = atlas[[;; , atlasCol["paramsReduced"]]], baseSurf, 
      typeLens, typeLenRepElem, colors}, 
    typeLens = Length /@ params;
    params = Flatten[params, 1];
    colors = 
    cyclicTakeUpTo[getDiscreteColorTheme[DefaultColor], Length[params]];
    typeLenRepElem = repelem[typeLens];
    Show[Table[
        baseSurf = params[[ii]];
        Switch[Length[baseSurf[[2]]], 
          0, 
          Graphics3D[{(*colors[[typeLenRepElem[[ii]]]]*)Purple, 
              Point[baseSurf[[1]]]}], 
          _, 
          plotParamPiece[baseSurf, vars, 
            PlotStyle -> colors[[typeLenRepElem[[ii]]]]]
        ]
        , {ii, Length[params]}], PlotRange -> All]
  ]

boundaryAtlasPolarParamsReduced[atlas_, vars_, ncList_] := 
  Module[{normalCones, generators}, 
    Inner[Function[{setInclusionIx, edge}, Table[
          normalCones = ncList[[setInclusionIx]];
          (* I want The convex hull of this: *)
          generators = 
          normalCones /. Thread[vars -> param[[1]]] // Simplify;
          Switch[Length[generators], 
            1, 
            {generators[[1]], param[[2]], param[[3]], {{0, 1}}}, 
            2, 
            {s generators[[1]] + (1 - s) generators[[2]], 
              Join[param[[2]], {s}], Join[param[[3]], {{0, 1}}]}, 
            _, 
            param(*Polygon[generators]*)(* Need to generalize above *)
          ]
          , {param, edge}]], atlas[[;; , atlasCol["regionIxs"]]], 
      atlas[[;; , atlasCol["paramsReduced"]]], List]
  ]

freeOptQ[expr_] := 
  And @@ (FreeQ[expr, #] & /@ {optFun, optMaxFun, optSet, optIntSet})
getPatterns[expr_, pat_] := 
  Last @ Reap[expr /. a : pat :> Sow[a], _, 
    Sequence @@ #2 &](* cases does not include head, even at level 0 *)


(* ::Input::Initialization:: *)
optCases[expr_] := 
  Flatten[getPatterns[
      expr, #] & /@ {_optFun, _optMaxFun, _optSet, _optIntSet}]

Options[objRelationGraph] = {TrivialEdges -> True};
objRelationGraph[f_, OptionsPattern[]] := Block[{g}, 
  visitedObjs = {};
  objQueue = {f};
  edgeList = {};
  
  While[Length[objQueue] > 0, 
    Block[{ff = objQueue[[1]]}, 
      relationalCandidates = Flatten[KeyValueMap[
          With[{cases = optCases[#2]}, 
            If[Length[cases] > 0, 
              Function[{case}, {ff, case, #1}] /@ cases, Missing[]]] &, 
          ff["data"]
        ] /. Missing[] -> Sequence[], 1];
      edgeList = Join[edgeList, DirectedEdge @@@ relationalCandidates];
      visitedObjs = Join[visitedObjs, {ff}];
      objQueue = DeleteCases[objQueue, ff];
      objQueue = 
      Join[objQueue, 
        Complement[relationalCandidates[[;; , 2]], visitedObjs]];
    ]
  ];
  
  g = Graph[edgeList, VertexLabels -> "Name", EdgeLabels -> "EdgeTag"];
  If[Not @ OptionValue[TrivialEdges], 
    g = EdgeDelete[g, 
      EdgeList[
        g][[Flatten @ 
          Position[
            SameQ[{}, #] & /@ StringCases[EdgeTags[g], ___ ~~ "Of"], 
            False]]]]];
  g
]

functionList[context_String : "Global`"] := 
  TableForm @ 
Sort[HoldForm @@@ 
  Flatten[(ToExpression[#, InputForm, DownValues] & /@ 
      Names[context <> "*"])[[All, All, 1]]]]


(* ::Input::Initialization:: *)
DEBUG = True;

(* basic stateful object that has inheritance *)
optObj[data_Association] := With[{ix = Unique[]}, 
  optObj[ix]["data"] = data;
  optObj[ix]
]
optObj[ix_]["get", prop_] := Lookup[optObj[ix]["data"], prop, 
  With[{newProp = optObj[ix]["init", prop]}, If[(*Not[First @ newProp === "init"]*)True, AppendTo[optObj[ix]["data"], prop -> newProp]]];
  optObj[ix]["data"][prop]
];
optObj[ix_][prop_String] := optObj[ix]["get", prop];
optObj[ix_]["init", prop_List] := 
  optObj[ix]["get", #] & /@ 
prop;(* useful, but highlights naming convention issue; get is \
  what actually inits things in the data... *)

optObj["initData", expr_, vars_] := Module[
  {exprTMP = expr, varsTMP = vars, 
    cnd}, 
  (*process and validate input*)
  If[SameQ[Head @ varsTMP, Symbol], 
    varsTMP = {vars}
  ];
  If[SameQ[Head @ exprTMP, List], 
    cnd = exprTMP[[2]]; exprTMP = exprTMP[[1]], 
    cnd = True; exprTMP = exprTMP
  ];
  <|"expr" -> exprTMP, "vars" -> varsTMP, "cnd" -> cnd|>];
optObj[expr_, vars_] := optObj[optObj["initData", expr, vars]]

(* methods *)
optID[optObj[ix_]] := ix;
isComputed[optObj[ix_], key_] := KeyExistsQ[optObj[ix]["data"], key];
nVars[optObj[ix_]] := Length[optObj[ix]["vars"]]
sub[optObj[ix_], val_] := 
  optObj[ix]["expr"] /. Thread[optObj[ix]["vars"] -> val]

DownValues[optFun] = 
ReplaceRepeated[DownValues[optObj], optObj -> optFun];
SubValues[optFun] = 
ReplaceRepeated[SubValues[optObj], optObj -> optFun];
sub[optFun[ix_], val_] := 
  optObj[ix]["expr"] /. Thread[optFun[ix]["vars"] -> val]
optFun[ix_]["init", "verbose"] := DEBUG
optFun[ix_]["init", "name"] := Subscript[\[FormalF], ix]

optFun[ix_]["init", "displayMode"] := "full"
(*Format[optFun[id_]] := Module[{hlRules, f = optFun[id], d0 = {}(*KeyDrop[\
          optFun[id]["data"], "parent"]*)}, 
    Switch[f["displayMode"], 
      "full", 
      hlRules = # -> Style[#, FontColor -> Blue, FontWeight -> Medium]& /@ f["vars"];
      Tooltip[Panel[Magnify[f["expr"] /. hlRules//TraditionalForm, 1.25], \
          FrameMargins -> 0, Background -> Lighter[Gray, 0.95]], d0], 
      "name", 
      Tooltip[Magnify[Style[f["name"], FontColor -> Red, FontWeight -> Medium]//\
          TraditionalForm, 1.25], d0]
  ]];*)

plotBoundsParser[vars_, bounds_ : {}] := 
  Module[{b = bounds, nVars}, nVars = Length[vars];
    (*infer bounds*)
    If[SameQ[b, {}], b = 1];
    (*default to unit box*)
    If[NumberQ[b], b = b*{-1, 1}];
    If[Length[b] == 2 && NumberQ[b[[1]]], b = Table[b, {nVars}]];
    b = Join[List /@ vars, b, 2]]
plot[optFun[ix_], bounds_ : {}, varargin___] := 
  Module[{f = optFun[ix], 
      b = plotBoundsParser[optFun[ix]["vars"], bounds]}, 
    (*TODO: make manipulate if there are parameters*)
    Switch[Length[f["vars"]], 
      1, Plot[f["expr"] // cvxReduce, Evaluate[Sequence @@ b], varargin], 
      2, Plot3D[f["expr"] // cvxReduce, Evaluate[Sequence @@ b], 
        varargin], 
      _, Missing[]]
  ]
cplot[optFun[ix_], bounds_ : {}, varargin___] := 
  Module[{f = optFun[ix], 
      b = plotBoundsParser[optFun[ix]["vars"], bounds]}, 
    (*TODO: make manipulate if there are parameters*)
    Switch[Length[f["vars"]], 
      1, Missing[], 
      2, ContourPlot[f["expr"] // cvxReduce, Evaluate[Sequence @@ b], 
        varargin], 
      3, ContourPlot3D[f["expr"] // cvxReduce, Evaluate[Sequence @@ b], 
        varargin], _, Missing[]]
  ]

optFun[ix_]["init", "parent"] := Null

optFun[ix_]["init", "lev"] := 
  Module[{f = optFun[ix], d = optFun[ix]["data"], dObj}, 
    dObj = initializeSet @@ lev[d["expr"], d["vars"], 1];
    
    If[! SameQ[d["convexity"], Indeterminate], 
      AppendTo[dObj["data"], "convex" -> True]];
    If[trep[d["expr"], d["vars"], ConstantArray[0, Length[d["vars"]]]] == 
      0 && dObj["contains0"], AppendTo[dObj["data"], "gauge" -> f]];(*
      3.3.11 *)
    
    dObj
  ]

optFun[ix_]["init", "convexity"] := 
  With[{d = optFun[ix]["data"]}, 
    FunctionConvexity[{d["expr"], d["cnd"]}, d["vars"]]]
optFun[ix_]["init", "convex"] := optFun[ix]["data"]["convexity"] === 1
optFun[ix_]["init", "domain"] := 
  With[{d = optFun[ix]["data"]}, 
    initializeSet @@ dom[d["expr"], d["vars"]]]
optFun[ix_]["init", "epi"] := 
  With[{d = optFun[ix]["data"]}, 
    initializeSet @@ epi[d["expr"], d["vars"]]]

DownValues[optMaxFun] = 
ReplaceRepeated[DownValues[optObj], optObj -> optMaxFun];
SubValues[optMaxFun] = 
ReplaceRepeated[SubValues[optObj], optObj -> optMaxFun];
sub[optMaxFun[ix_], val_] := 
  optMaxFun[ix]["expr"] /. Thread[optMaxFun[ix]["vars"] -> val]
optMaxFun[ix_]["init", "verbose"] := DEBUG

optMaxFun[ix_]["init", "children"] := 
  Module[{parts = optMaxFun[ix]["expr"] /. Max -> List, children, 
      myName}, 
    children = 
    If[Head[#] === optFun, #, optFun[#, optMaxFun[ix]["vars"]]] & /@ 
    parts;
    AppendTo[optMaxFun[ix]["data"], 
      "expr" -> Max @@ (#["expr"] & /@ children)];(*
      inheritance is kind of tricky when *)
    myName = optMaxFun[ix]["name"];
    MapIndexed[
      AppendTo[#1["data"], 
        "name" -> Subscript[myName, #2[[1]]] /. 
        Subscript[a_, Subscript[b_, c_]] :> Subscript[a, {b, c}]] &, 
      children];
    Map[AppendTo[#1["data"], "parent" -> optMaxFun[ix]] &, children];
    (*Map[AppendTo[#1["data"], "displayMode" -> "name"]&, children];*)
    children
  ]
optMaxFun[ix_]["init", "name"] := Subscript[\[FormalF], ix]

(*Format[optMaxFun[id_]] := Module[{hlRules, d0 = \
      KeyDrop[optMaxFun[id]["data"], "children"], c = \
      optMaxFun[id]["data"]["children"]}, 
    Tooltip[Panel[c /. List -> CirclePlus]//TraditionalForm, d0]]*)

optMaxFun[ix_]["init", "epi"] := 
  Module[{c = optMaxFun[ix]["children"]}, 
    initializeSet[Fold[And, #["epi"]["expr"] & /@ c], 
      c[[1]]["epi"]["vars"], Name -> epi[optMaxFun[ix]["name"]]]]

plot[optMaxFun[ix_], bounds_ : {}, varargin___] := 
  Module[{f = optMaxFun[ix], 
      b = plotBoundsParser[optMaxFun[ix]["vars"], bounds]}, 
    (*TODO: make manipulate if there are parameters*)
    Switch[Length[f["vars"]], 
      1, Plot[f["expr"] // cvxReduce, Evaluate[Sequence @@ b], varargin], 
      2, Plot3D[f["expr"] // cvxReduce, Evaluate[Sequence @@ b], 
        varargin], 
      _, Missing[]]
  ]
cplot[optMaxFun[ix_], bounds_ : {}, varargin___] := 
  Module[{f = optMaxFun[ix], 
      b = plotBoundsParser[optMaxFun[ix]["vars"], bounds]}, 
    (*TODO: make manipulate if there are parameters*)
    Switch[Length[f["vars"]], 
      1, Missing[], 
      2, ContourPlot[f["expr"] // cvxReduce, Evaluate[Sequence @@ b], 
        varargin], 
      3, ContourPlot3D[f["expr"] // cvxReduce, Evaluate[Sequence @@ b], 
        varargin], _, Missing[]]
  ]

DownValues[optSet] = 
ReplaceRepeated[DownValues[optObj], optObj -> optSet];
SubValues[optSet] = 
ReplaceRepeated[SubValues[optObj], optObj -> optSet];

sub[optSet[ix_], val_] := 
  optSet[ix]["expr"] /. Thread[optSet[ix]["vars"] -> val]
optID[optSet[ix_]] := ix;
isComputed[optSet[ix_], key_] := KeyExistsQ[optSet[ix]["data"], key];
nVars[optSet[ix_]] := Length[optSet[ix]["vars"]]
optSet[ix_]["init", "verbose"] := DEBUG

(*Format[optSet[id_]] := Module[{hlRules, f = optSet[id], d0 = {}(*KeyDrop[\
          optSet[id]["data"], "parent"]*)}, 
    Switch[f["displayMode"], 
      "full", 
      hlRules = # -> Style[#, FontColor -> Blue, FontWeight -> Medium]& /@ f["vars"];
      Tooltip[Panel[Magnify[f["expr"] /. hlRules//TraditionalForm, 1.25], \
          FrameMargins -> 0], d0], 
      "name", 
      Tooltip[Magnify[Style[f["name"], FontColor -> Purple, FontWeight -> Medium]//\
          TraditionalForm, 1.25], d0]
  ]];*)

optSet[ix_]["init", "name"] := Subscript[C, ix]
optSet[ix_]["init", "displayMode"] := "full"

plot[optSet[ix_], bounds_ : {}, varargin___] := 
  Module[{f = optSet[ix], 
      b = plotBoundsParser[optSet[ix]["vars"], bounds]}, 
    (*TODO: make manipulate if there are parameters*)
    Switch[Length[f["vars"]], 
      2, RegionPlot[f["expr"] // cvxReduce, Evaluate[Sequence @@ b], 
        varargin], 
      3, RegionPlot3D[f["expr"] // cvxReduce, Evaluate[Sequence @@ b], 
        varargin], 
      _, Missing[]]
  ]

plot[optISet[ix_], bounds_ : {}, varargin___] := 
  Module[{f = optISet[ix], 
      b = plotBoundsParser[optISet[ix]["vars"], bounds]}, 
    (*TODO: make manipulate if there are parameters*)
    Switch[Length[f["vars"]], 
      2, RegionPlot[f["expr"] // cvxReduce, Evaluate[Sequence @@ b], 
        varargin], 
      3, RegionPlot3D[f["expr"] // cvxReduce, Evaluate[Sequence @@ b], 
        varargin], 
      _, Missing[]]
  ]

optISet[ix_]["init", "parent"] := Null

optSet[ix_]["init", "name"] := Subscript[C, ix]
optSet[ix_]["init", "displayMode"] := "full"
optSet[ix_]["init", "contains0"] := 
  With[{f = optSet[ix]}, 
    Reduce[Implies[f["cnd"], 
        Reduce[sub[f, Table[0, Length[f["vars"]]]]]], f["vars"], Reals]]
optSet[ix_]["init", "bounded"] := 
  With[{f = optSet[ix]}, 
    Reduce[Implies[f["cnd"], bounded[cvxReduce[f["expr"]], f["vars"]]], 
      f["vars"], Reals]]

DownValues[optIntSet] = 
ReplaceRepeated[DownValues[optObj], optObj -> optIntSet];
SubValues[optIntSet] = 
ReplaceRepeated[SubValues[optObj], optObj -> optIntSet];
sub[optIntSet[ix_], val_] := 
  optIntSet[ix]["expr"] /. Thread[optIntSet[ix]["vars"] -> val]
optIntSet[ix_]["init", "verbose"] := DEBUG

(*Format[optIntSet[id_]] := Module[{hlRules, d0 = optIntSet[id]["data"], c = \
      optIntSet[id]["data"]["children"]}, Tooltip[Panel[c /. \
        List -> And]//TraditionalForm, d0]]*)

optIntSet[ix_]["init", "children"] := 
  Module[{parts = optIntSet[ix]["expr"] /. And -> List, children, 
      myName}, 
    Assert[AllTrue[parts, Head[#] === LessEqual &]];
    children = 
    optSet[#[[1]] - #[[2]] + 1 <= 1, optIntSet[ix]["vars"]] & /@ parts;
    myName = optIntSet[ix]["name"];
    MapIndexed[
      AppendTo[#1["data"], 
        "name" -> Subscript[myName, #2[[1]]] /. 
        Subscript[a_, Subscript[b_, c_]] :> Subscript[a, {b, c}]] &, 
      children];
    Map[AppendTo[#1["data"], "parent" -> optIntSet[ix]] &, children];
    (*Map[AppendTo[#1["data"], "displayMode" -> "name"]&, children];*)
    children
  ]
optIntSet[ix_]["init", "name"] := Subscript[C, ix]

plot[optIntSet[ix_], bounds_ : {}, varargin___] := 
  Module[{f = optIntSet[ix], 
      b = plotBoundsParser[optIntSet[ix]["vars"], bounds]}, 
    (*TODO: make manipulate if there are parameters*)
    Switch[Length[f["vars"]], 
      2, RegionPlot[f["expr"] // cvxReduce, Evaluate[Sequence @@ b], 
        varargin], 
      3, RegionPlot3D[f["expr"] // cvxReduce, Evaluate[Sequence @@ b], 
        varargin], 
      _, Missing[]]
  ]
boundaryPlot[optIntSet[ix_], varargin___] := 
  Module[{f = optIntSet[ix]}, 
    (*TODO: make manipulate if there are parameters*)
    boundaryAtlasPlot[f["boundaryAtlas"], f["vars"]]
  ]

optIntSet[ix_]["init", "contains0"] := 
  Module[{c = optIntSet[ix]["children"]}, 
    Reduce[And @@ Map[#["contains0"] &, c]]]
optIntSet[ix_]["init", "bounded"] := 
  Module[{c = optIntSet[ix]["children"]}, 
    If[Reduce[And @@ Map[#["bounded"] &, c]] === True, True, 
      With[{f = optIntSet[ix]}, bounded[f["expr"], f["vars"]]]
  ]]
optIntSet[ix_]["init", "gauge"] := 
  Module[{c = optIntSet[ix]["children"], d = optIntSet[ix]["data"]}, 
    initializeFunction[Max[Map[#["gauge"] &, c]], d["vars"]]
  ]
optIntSet[ix_]["init", "ncList"] := 
  Module[{c = optIntSet[ix]["children"], d = optIntSet[ix]["data"]}, 
    Map[#["normalizedNormalCone"] &, c]
  ]

optIntSet[ix_]["init", "boundaryAtlas"] := 
  Module[{obj = optIntSet[ix]}, boundaryAtlas[obj["expr"], obj["vars"]]]

project[optIntSet[ix_], x_] := x/sub[optIntSet[ix]["gauge"], x]

DownValues[optISet] = ReplaceRepeated[DownValues[optObj], optObj -> optISet];
SubValues[optISet] = ReplaceRepeated[SubValues[optObj], optObj -> optISet];
sub[optISet[ix_], val_] := optISet[ix]["expr"] /. Thread[optISet[ix]["vars"] -> val]

Format[optISet[id_]] := Module[{hlRules, f = optISet[id]}, 
  hlRules = # -> Style[#, FontColor -> Blue, FontWeight -> Medium] & /@ f["vars"];
  PopupWindow[
    Panel[Magnify[f["expr"] /. hlRules // TraditionalForm, 1.25], 
      FrameMargins -> 0], 
    f["data"], 
    WindowTitle -> "optISet " <> ToString @ id]]

DownValues[optDSet] = ReplaceRepeated[DownValues[optObj], optObj -> optDSet];
SubValues[optDSet] = ReplaceRepeated[SubValues[optObj], optObj -> optDSet];
sub[optDSet[ix_], val_] := optDSet[ix]["expr"] /. Thread[optDSet[ix]["vars"] -> val]

Options[initializeFunction] = {Conditions -> True, Name -> Automatic}
initializeFunction[{f_, cnds_}, vars_, OptionsPattern[]] := 
  initializeFunction[f, vars, 
    Sequence @@ (
      If[#1 === Conditions, 
        #1 -> 
        cnds && Element[Alternatives @@ vars, Reals] && 
          OptionValue[#1] // Simplify, 
        #1 -> OptionValue[#1]
      ] & @@@ Options[initializeFunction]
      )]
initializeFunction[f_, vars_, OptionsPattern[]] := Module[{f0}, 
  f0 = optFun[{f, OptionValue[Conditions]}, vars];
  If[Not[OptionValue[Name] === Automatic], 
    AppendTo[f0["data"], "name" -> OptionValue[Name]]];
  f0
]
initializeFunction[f_Max, vars_, OptionsPattern[]] := Module[{F0}, 
  F0 = optMaxFun[{f, OptionValue[Conditions]}, vars];
  If[Not[OptionValue[Name] === Automatic], 
    AppendTo[F0["data"], "name" -> OptionValue[Name]]];
  F0["children"];
  F0
]


(* ::Input::Initialization:: *)
Options[initializeSet] = {Conditions -> True, Name -> Automatic}
initializeSet[{f_, cnds_}, vars_, OptionsPattern[]] := 
  initializeSet[f, vars, 
    Sequence @@ (
      If[#1 === Conditions, 
        #1 -> 
        cnds && Element[Alternatives @@ vars, Reals] && 
          OptionValue[#1] // Simplify, 
        #1 -> OptionValue[#1]
      ] & @@@ Options[initializeSet]
      )]

initializeSet[f_GreaterEqual, vars_, OptionsPattern[]] := 
  initializeSet[-f[[2]] <= f[[1]], vars, 
    Sequence @@ (#1 -> OptionValue[#1] & @@@ Options[initializeSet])]
initializeSet[f_LessEqual, vars_, OptionsPattern[]] := Module[{f0}, 
  f0 = optSet[{f, OptionValue[Conditions]}, vars];
  If[Not[OptionValue[Name] === Automatic], 
    AppendTo[f0["data"], "name" -> OptionValue[Name]]];
  f0
]
initializeSet[f_And, vars_, OptionsPattern[]] := Module[{F0}, 
  F0 = optIntSet[{f, OptionValue[Conditions]}, vars];
  If[Not[OptionValue[Name] === Automatic], 
    AppendTo[F0["data"], "name" -> OptionValue[Name]]];
  F0["children"];
  F0
]


(* ::Input::Initialization:: *)
optSet[ix_]["init", "support"] := 
  Module[{f = optSet[ix], d = optSet[ix]["data"], sol, dObj, 
      polarReccCnds}, 
    Echo[{FreeQ[d["expr"], indicator], f["bounded"]}, {f["name"], 
        "Support"}];
    
    If[FreeQ[d["expr"], indicator] || f["bounded"] === True, 
      
      sol = simpleSupport[d["expr"] /. indicator[_] -> 0, d["vars"]];
      
      If[! FreeQ[sol, formalVector[d["vars"]][[1]]], 
        If[f["verbose"], 
          Echo[StringForm[
              "Support computation of `` using stationarySupport failed: \
              ``", {d["expr"] /. indicator[_] -> 0, d["vars"]}, sol], {f["name"], 
            "Support"}]];
      (* TODO: better control flow *)
      sol = support[d["expr"] // cvxReduce, d["vars"]];
      If[f["verbose"], 
        Echo[StringForm["Support `` computed directly", sol], {f["name"], 
            "Support"}]];
      , 
      If[f["verbose"], 
        Echo[StringForm["Support `` computed using stationarySupport", 
            sol], {f["name"], "Support"}]];
    ];
    
    If[! f["bounded"], 
      
      (*If[isComputed[f, "gauge"], Echo[f["gauge"]]];*)
      
      If[f["contains0"] && isComputed[f, "gauge"], 
        (* Basu, A. 3.3.11 *)
        polarReccCnds = 
        polar[Reduce[f["gauge"]["expr"] == 0 // cvxReduce, 
            f["gauge"]["vars"], Reals], f["gauge"]["vars"]];
        If[f["verbose"], 
          Echo[StringForm["polarReccCnds `` computed using gauge", 
              polarReccCnds], {f["name"], "Support"}]];
        , 
        polarReccCnds = polarRecc[d["expr"] // cvxReduce, d["vars"]];
        If[f["verbose"], 
          Echo[StringForm["polarReccCnds `` computed directly", 
              polarReccCnds], {f["name"], "Support"}]];
      ];
      
      (*Echo[{polarReccCnds}];*)
      sol = 
      Assuming[polarReccCnds[[1]] && d["cnd"], Simplify[sol]] +
      indicator[polarReccCnds[[1]]]
    ]
    , 
    sol = support[d["expr"] // cvxReduce, d["vars"]];
    If[f["verbose"], 
      Echo[StringForm["Support `` computed directly", sol], {f["name"], 
          "Support"}]];
  ];

Echo[List[sol, 
    Fold[And, Element[#, Reals] & /@ d["vars"]] && d["cnd"]]];
dObj = initializeFunction[{FullSimplify[sol, 
      Fold[And, Element[#, Reals] & /@ d["vars"]] && d["cnd"]], 
    d["cnd"]}, d["vars"], Name -> \[Sigma][f["name"]]];
Echo[dObj["expr"], {f["name"], "Support"}];
If[True, AppendTo[dObj["data"], "supportOf" -> f]];

dObj
]
optSet[ix_]["init", "polar"] := 
  Module[{f = optSet[ix], d = optSet[ix]["data"], dObj, polarGauge, 
      polarExpr}, 
    polarGauge = f["support"];
    polarExpr = 
    FullSimplify[
      cvxResolveOverReals[polarGauge["expr"] <= 1, d["vars"], d["cnd"]], 
      d["cnd"]];
    
    dObj = initializeSet[{polarExpr, d["cnd"]}, 
      f["vars"](*formalCovector[f["vars"]]*), Name -> polar[f["name"]]];
    If[! f["contains0"], 
      (*Echo[contains0polar];*)
      polarGauge = 
      initializeFunction[Max[polarGauge, 0], f["vars"], 
        Name -> gauge[polar[f["name"]]]]
    ];
    
    (*If[True, AppendTo[dObj["data"], "polarOf" -> f]];*)
    
    If[True, AppendTo[polarGauge["data"], "lev" -> dObj]];
    If[True, AppendTo[dObj["data"], "gauge" -> polarGauge]];
    (*If[f["contains0"], AppendTo[dObj["data"], "bounded" -> True]];*)(*
      this has to be stated for optSet[x^2-y-1 <= 1 /. Thread[{x, y} -> 
          RotationMatrix[0].({x, y}-1/8)], {x, y}]["polar"], 
      removed for epi graphs *)
    If[isComputed[f, "polarOf"], 
      AppendTo[dObj["data"], "zeroHull" -> f["polarOf"]]];
    
    If[f["contains0"], AppendTo[dObj["data"], "polar" -> f]
    ];
    
    dObj
  ]
optSet[ix_]["init", "gauge"] := 
  Module[{f = optSet[ix], d = optSet[ix]["data"], dObj, polarGauge}, 
    dObj = optSet[ix]["polar"]["support"];
    If[True, AppendTo[dObj["data"], "lev" -> f]];
    dObj
  ]
optSet[ix_]["init", "normalizedNormalCone"] := 
  Grad[optSet[ix]["gauge"]["expr"], optSet[ix]["vars"]]

formatMode = "dynamic";
setOptFormat[formatMode_] := Switch[formatMode, 
  "bare", (FormatValues[#] = {}) & /@ {optFun, optMaxFun, optSet, 
    optIntSet};, 
  "expr", 
  (*optInstance[_, _, ix_, h_] := h[ix];*)
  exprFormater[(f_optFun | f_optMaxFun | f_optSet | f_optIntSet)] := 
    optInstance[f["expr"], f["vars"], f[[1]], Head @ f];
  Format[optFun[id_]] := exprFormater[optFun[id]];
  Format[optMaxFun[id_]] := exprFormater[optMaxFun[id]];
  Format[optSet[id_]] := exprFormater[optSet[id]];
  Format[optIntSet[id_]] := exprFormater[optIntSet[id]];, 
  "noButton", 
  formatExpr[optFun[id_]] := Module[{hlRules, f = optFun[id]}, 
    hlRules = # -> 
    Style[#, FontColor -> Blue, FontWeight -> Medium] & /@ 
    f["vars"];
    Panel[Magnify[f["expr"] /. hlRules // TraditionalForm, 1.25], 
      FrameMargins -> 0, Background -> Lighter[Gray, 0.95]]
  ];
  formatExpr[optSet[id_]] := Module[{hlRules, f = optSet[id]}, 
    hlRules = # -> 
    Style[#, FontColor -> Blue, FontWeight -> Medium] & /@ 
    f["vars"];
    Panel[Magnify[f["expr"] /. hlRules // TraditionalForm, 1.25], 
      FrameMargins -> 0]
  ];
  formatExpr[optMaxFun[id_]] := 
    Module[{f = optMaxFun[id], c = optMaxFun[id]["children"]}, 
      Panel[CirclePlus @@ Deploy /@ c, FrameMargins -> 0]
    ];
  formatExpr[optIntSet[id_]] := 
    Module[{f = optIntSet[id], c = optIntSet[id]["children"]}, 
      Panel[And @@ Deploy /@ c, FrameMargins -> 0]
    ];
  formatName[(f_optFun | f_optMaxFun)] := 
    Style[f["name"], FontColor -> Blue, FontWeight -> Medium];
  formatName[(f_optSet | f_optIntSet)] := 
    Style[f["name"], FontColor -> Purple, FontWeight -> Medium];
  (*(h_optFun|h_optMaxFun|h_optSet|h_optIntSet)*)
  dynamicOptFormater[(f_optFun | f_optMaxFun | f_optSet |
      f_optIntSet)] := 
    Tooltip[formatExpr[f], {Head[f], f[[1]], f["name"]}];
  Format[optFun[id_]] := dynamicOptFormater[optFun[id]];
  Format[optMaxFun[id_]] := dynamicOptFormater[optMaxFun[id]];
  Format[optSet[id_]] := dynamicOptFormater[optSet[id]];
  Format[optIntSet[id_]] := dynamicOptFormater[optIntSet[id]];, 
  "dynamic", 
  formatExpr[optFun[id_]] := Module[{hlRules, f = optFun[id]}, 
    hlRules = # -> 
    Style[#, FontColor -> Blue, FontWeight -> Medium] & /@ 
    f["vars"];
    Panel[Magnify[f["expr"] /. hlRules // TraditionalForm, 1.25], 
      FrameMargins -> 0, Background -> Lighter[Gray, 0.95]]
  ];
  formatExpr[optSet[id_]] := Module[{hlRules, f = optSet[id]}, 
    hlRules = # -> 
    Style[#, FontColor -> Blue, FontWeight -> Medium] & /@ 
    f["vars"];
    Panel[Magnify[f["expr"] /. hlRules // TraditionalForm, 1.25], 
      FrameMargins -> 0]
  ];
  formatExpr[optMaxFun[id_]] := 
    Module[{f = optMaxFun[id], c = optMaxFun[id]["children"]}, 
      Panel[CirclePlus @@ Deploy /@ c, FrameMargins -> 0]
    ];
  formatExpr[optIntSet[id_]] := 
    Module[{f = optIntSet[id], c = optIntSet[id]["children"]}, 
      Panel[And @@ Deploy /@ c, FrameMargins -> 0]
    ];
  formatName[(f_optFun | f_optMaxFun)] := 
    Style[f["name"], FontColor -> Blue, FontWeight -> Medium];
  formatName[(f_optSet | f_optIntSet)] := 
    Style[f["name"], FontColor -> Purple, FontWeight -> Medium];
  (*(h_optFun|h_optMaxFun|h_optSet|h_optIntSet)*)
  dynamicOptFormater[(f_optFun | f_optMaxFun | f_optSet |
      f_optIntSet)] := 
    DynamicModule[{showingPanel = False, usingNames = False, 
        tabChoice = 1}, 
      Dynamic[Refresh[DynamicModule[{nameDisplay, selectorPanel}, 
            nameDisplay = If[usingNames, formatName[f], formatExpr[f]];
            selectorPanel = 
            Tooltip[Toggler[
                Dynamic[showingPanel], # -> nameDisplay & /@ {True, False}], 
              {Head[f], f[[1]], f["name"]}];
            Column[{
                selectorPanel, 
                Sequence @@ If[! showingPanel, {}, {TabView[{
                        "DataSet" -> Dataset[f["data"]], 
                        "Plots" -> Dynamic[Refresh[
                            If[tabChoice == 2, 
                              (* [Preset dropdown] [code textbox] [copy button] [
                                  evaluate button]*)
                              plot[f], 
                              "Generating ..."]
                            , TrackedSymbols :> {tabChoice}]]
                      }, Dynamic[tabChoice], FrameMargins -> 0]}]
            }]
          ], TrackedSymbols :> {showingPanel}]]
    ];
  Format[optFun[id_]] := dynamicOptFormater[optFun[id]];
  Format[optMaxFun[id_]] := dynamicOptFormater[optMaxFun[id]];
  Format[optSet[id_]] := dynamicOptFormater[optSet[id]];
  Format[optIntSet[id_]] := dynamicOptFormater[optIntSet[id]];
]
setOptFormat["noButton"]

simpleSupport[cons_LessEqual, vars_] := 
  Module[{newVars = formalVector[vars], exprNew, sols}, 
    (* assumes cons is convex, bounded, and contains 0 *)
    exprNew = cons /. Thread[vars -> newVars];
    sols = lagrangeStationaryPoints[vars . newVars, 
      exprNew /. LessEqual -> Equal, newVars];
    Echo[sols];
    Simplify[FullSimplify @ Max[sols], 
      Element[Alternatives @@ vars, Reals]]
  ]

optSet[ix_]["init", "boundaryAtlas"] := 
  Module[{obj = optSet[ix]}, boundaryAtlas[obj["expr"], obj["vars"]]]

optISet[ix_]["init", "contains0"] := 
  With[{f = optISet[ix]}, Reduce[sub[f, Table[0, Length[f["vars"]]]]]]
optISet[ix_]["init", "pSet"] := 
  Module[{f = optISet[ix], d = optISet[ix]["data"], def, dObj, 
      bdryParam, sol, t}, def = d["expr"];
    If[Length[f["vars"]] == 2 && 
        SameQ[f["contains0"], True], (*thispartneedsalotofwork*)
      sol = Solve[{def, Cos[t] f["vars"][[2]] == Sin[t] f["vars"][[1]]}, 
        f["vars"], Reals];
      If[Length @ sol == 2, (*assumerootobjectssplitalongx-axis*)
        bdryParam = 
        Simplify[
          Piecewise @ 
          Transpose @ {f["vars"] /. sol, {Pi <= t <= 2 Pi, 
              0 <= t < Pi}}], (*assumesinglesolution*)
        bdryParam = f["vars"] /. sol, bdryParam = f["vars"] /. sol];];
    dObj = optPSet[{bdryParam, f["cnd"]}, f["vars"]]]
optISet[ix_]["init", "bounded"] := 
  Block[{f = optISet[ix], d = optISet[ix]["data"], B, out}, 
    Resolve[Exists[B, 
        ForAll[Evaluate[d["vars"]], f["expr"], 
          d["vars"] . d["vars"] <= B]]]]
optISet[ix_]["init", "conicHullCnds"] := 
  Block[{f = optISet[ix], d = optISet[ix]["data"], B, out}, 
    Exists[\[Lambda], \[Lambda] > 0, 
      f["expr"] /. Thread[f["vars"] -> \[Lambda]f["vars"]]] // Reduce //
    FullSimplify]
optISet[ix_]["init", "reccCnds"] := 
  Module[{f = optISet[ix], d = optISet[ix]["data"], B, out, newVars, x, 
      reccCnd}, newVars = Array[Subscript[x, #] &, Length[f["vars"]]];
    reccCnd = 
    ForAll[Evaluate[newVars], 
      f["expr"] /. Thread[f["vars"] -> newVars], 
      f["expr"] /. Thread[f["vars"] -> newVars + f["vars"]]];
    Reduce[reccCnd, newVars, Reals]]
optISet[ix_]["init", "polarReccCnds"] := 
  Module[{f = optISet[ix], d = optISet[ix]["data"], B, out, newVars, x, 
      pPeccCnd}, newVars = Array[Subscript[x, #] &, Length[f["vars"]]];
    pPeccCnd = 
    ForAll[Evaluate[newVars], 
      f["reccCnds"] /. Thread[f["vars"] -> newVars], 
      f["vars"] . newVars <= 1];
    Reduce[pPeccCnd, newVars, Reals]]
optISet[ix_]["init", "support"] := 
  Module[{f = optISet[ix], d = optISet[ix]["data"], def, dObj, 
      bdryParam, sol, sols, x, newVars, exprnew, lhs, cnd}, (*sol = 
      Maximize[{f["vars"].newVars, f["expr"] /. Thread[f["vars"] -> newVars]}, 
        newVars, Reals][[1]]//FullSimplify;(*thisbreaksthedomaindownbadly*)*)
    newVars = Array[Subscript[x, #] &, Length[f["vars"]]];
    (*hotfixforunboundedsets.TODO:formalizewithindicators*)
    exprnew = sub[f, newVars];
    lhs = exprnew[[1]];
    {lhs, cnd} = 
    If[Head @ lhs === Piecewise, 
      lhs /. {Piecewise[{{a_, c_}}, DirectedInfinity[1]] :> {a, 
          c}}, {lhs, True}];
    (*Echo[{optISet[ix], lhs}];*)sols = f["vars"] . newVars /. 
    Solve[
      Eliminate[
        D[f["vars"] . newVars - \[Lambda] (exprnew[[2]] - lhs), {Join[
              newVars, {\[Lambda]}]}] == 0, \[Lambda]], newVars];
    (*Echo[{optISet[ix], sols, dObj}];*)(*Which[And[f["contains0"], f[
            "bounded"]], sol = Simplify[FullSimplify @ Max[sols], Element[
            Alternatives @@ f["vars"], Reals]], !f["contains0"], Echo[{exprnew, sols, 
            D[f["vars"].newVars-\[Lambda](exprnew[[2]]-lhs), {Join[
                  newVars, {\[Lambda]}]}] == 0}];
        sol = FullSimplify @ Piecewise[Transpose @ {sols, Reduce[#>0, f1["vars"], 
              Reals]& /@ sols}, Infinity];
        sol = Simplify[FullSimplify @ Max[sols], Element[Alternatives @@ f["vars"], 
            Reals]], True, sol = FullSimplify @ Piecewise[Transpose @ {sols, Reduce[# >= 0, 
              f1["vars"], Reals]& /@ sols}, Infinity]];*)Echo[sols];
    sol = Simplify[FullSimplify @ Max[sols], 
      Element[Alternatives @@ f["vars"], Reals]];
    If[Not[f["bounded"]], 
      sol = Piecewise[{{Assuming[f["polarReccCnds"], FullSimplify[sol]], 
            f["polarReccCnds"]}}, Infinity]];
    dObj = optFun[{sol, f["cnd"]}, f["vars"]];
    dObj]
optISet[ix_]["init", "polar"] := 
  Module[{f = optISet[ix], d = optISet[ix]["data"], def, dObj, 
      bdryParam, sol, x, newVars, support}, support = f["support"];
    dObj = 
    optISet[{support["expr"] <= 1, support["cnd"]}, support["vars"]];
    (*(!Contains0) = >DomGaugeisconichull*)(*(!Contains0) = >max(support, 
        0)ispolargauge, butpolarcanbedefinedthesame, simpler, way*)(*If[Not[f[
            "contains0"]], supportNew = Piecewise[{{Assuming[f["conicHullCnds"], 
                FullSimplify[Max[support["expr"], 0]]], f["conicHullCnds"]}}, 
          Infinity];Echo[{supportNew, f["conicHullCnds"]}]];*)
    AppendTo[dObj["data"], "gauge" -> support];
    (*AppendTo[dObj["data"], "reccCnds" -> f["polarReccCnds"]];
      AppendTo[dObj["data"], "polarReccCnds" -> f["reccCnds"]];*)dObj];
optISet[ix_]["init", "gauge"] := optISet[ix]["polar"]["support"]
optISet[ix_]["init", "normalizedNormalCone"] := 
  Grad[optISet[ix]["gauge"]["expr"], optISet[ix]["vars"]]


(* ::Section:: *)
(*Region Management*)


(* ::Subsection:: *)
(*ir (Implicit Region) Functions*)


PackageExport["irSame"]
PackageExport["irDeleteDuplicates"]
PackageExport["irPos"]
PackageExport["irPosContains"]
PackageExport["irListIntersetDMinus1"]
PackageExport["irBuildSubsetGraph"]
PackageExport["irsgEnumGaugeList"]
PackageExport["irsgEnumProblems"]

irSame[ir1_, ir2_] := Reduce[Equivalent[ir1[[1]], ir2[[1]]], Evaluate[uJoin[ir1[[2]], ir2[[2]]]], Reals] === True
irSame[ir1_EmptyRegion, ir2_ImplicitRegion] := False
irSame[ir1_ImplicitRegion, ir2_EmptyRegion] := False

irDeleteDuplicates[irList_] := DeleteDuplicates[irList, irSame]
irPos[irList_, ir0_] := Position[(irSame[#1, ir0] & ) /@ irList, True]
irPosContains[irList_, x_] := Position[(RegionMember[#1, x] & ) /@ irList, True]


irListIntersetDMinus1[irList_] := irDeleteDuplicates[
  Flatten[Table[
      RegionIntersection[irList[[i]], irList[[j]]], 
      {i, Length[irList]}, {j, i + 1, Length[irList]}]]
 /. EmptyRegion[_] -> Sequence[] (* empty regions appear if low dims are disjoint *)
]

irBuildSubsetGraph[irList_] := Module[{
    regAll, intMat, pathPairs, irsgDir, pathGraph
  }, 
  (* get all intersections down to lowest dim *)
  regAll = irDeleteDuplicates[Flatten[NestList[irListIntersetDMinus1[#1] & , irList, 2]] /. EmptyRegion[_] -> Sequence[]];
  intMat = Outer[irPos[regAll, RegionIntersection[#1, #2]] & , regAll, regAll];
  pathPairs = Flatten[MapApply[
      Function[{list, ix}, ({ix, #} -> 1 &) /@ DeleteDuplicates[Flatten[list]]], 
      ({intMat, Range[Length[intMat]]}\[Transpose])] /. ({x_, x_} -> 1) -> Sequence[]];
  irsgDir = AdjacencyGraph[SparseArray[pathPairs, Max[intMat]]];
  pathGraph = UndirectedGraph[irsgDir];
  {irsgDir, regAll}
]


irsgEnumGaugeList[gaugesHighDim_, irListHighDim_, irsgDir_] := Module[{
    nRegHD, nReg, gIxs, gFuns, gDims
  }, 
  (* p1 and p2 are assumed to be numeric *)
  nRegHD = Length[irListHighDim];
  nReg = VertexCount[irsgDir];
  (* all that matters is that the top level of gDir are the top dims, otherwise would have to do a fancy check on who doesn't have incomponents or some other graph theory stuff *)
  gIxs = Join[Range[nRegHD], (Select[VertexInComponent[irsgDir, #1], #1 <= nRegHD & ] & ) /@ Range[nRegHD + 1, nReg]];
  gFuns = (If[Head[#1] === List, Function[x, Evaluate[Min @@ (#1[x] & ) /@ gaugesHighDim[[#1]]]], gaugesHighDim[[#1]]] & ) /@ gIxs;
  
  (* TODO: profile against RegionDimension /@ regAll and just make a function *)
  gDims = RegionEmbeddingDimension[irListHighDim[[1]]]-((LongestOutComponentPath[ReverseGraph[irsgDir], #1] & ) /@ Range[VertexCount[irsgDir]]);
  ((gFuns[[#1]] = 0 & ) & ) /@ Position[gDims, 0, 1]; (*regions of zero dim don't need gauges*)
  
  gFuns
]

irsgEnumProblems[p0_, p1_, gaugesAll_, irListAll_, irsgDir_] := Module[{
    irIx0, irIx1, g, paths, gDims, subVars, subVarCnds, pointList, gaugeSum, ans
  }, 
  irIx0 = irPosContains[irListAll, p0][[1, 1]];
  irIx1 = irPosContains[irListAll, p1][[1, 1]];
  
  g = UndirectedGraph[irsgDir];
  paths = FindPath[g, irIx0, irIx1, All, All];
  (* below formula only works if graph has terminal object:
    gDims = (LongestOutComponentPath[irsgDir, #1] & ) /@ Range[VertexCount[irsgDir]]; *)
  gDims = RegionDimension /@ regAll;
  paths = paths /. (#1 -> Sequence[] & ) /@ Flatten[Position[gDims, 0, 1]];
  
  ans = Table[
    (* now we want to solve for the nth path (so we can put in a loop and update dynamically)*)
    (* we only need sub variables for "inner" regions of the path because p0 and p1 come from path[[1]] and path[[-1]] *)
    subVars = ({Indexed[s1, #1], Indexed[s2, #1]} & ) /@ Range[Length[path] - 1]; (* todo: higher dims *)
    subVarCnds = (Reduce[RegionMember[#2[[1]], #1] && RegionMember[#2[[2]], #1], #1, Reals] & ) @@@ Transpose[{subVars, Partition[irListAll[[path]], 2, 1]}];
    (* might want to remove reduce to assume *)
    subVarCnds = And @@ subVarCnds;
    pointList = Partition[Join[{p0}, subVars, {p1}], 2, 1];
    gaugeSum = Total[(gaugesAll[[#2]][#1[[2]] - #1[[1]]] & ) @@@ Transpose[{pointList, path}]];
    {gaugeSum, subVarCnds, Flatten[subVars], pointList}
    , {path, paths}];
  Transpose[Join[Transpose[ans], {paths}]]
]


(* ::Section:: *)
(*pwl Functions*)

PackageExport["pwlMaxSurf2lcon"]
PackageExport["pwlSurf2vertR3"]
PackageExport["lcon2vert"]
PackageExport["vellHull2pwlMaxSurf"]
PackageExport["vellHull2lcon"]
PackageExport["lcon2pwlMaxSurf"]
PackageExport["pwlMaxSurf2vert"]
PackageExport["infConv3D"]
PackageExport["meshFacesInRegion"]
PackageExport["meshFaces"]

pwlMaxSurf2lcon[Max[s__], cutZ_:Infinity] := Module[{
    bentSurf = Max[s], 
    A, b, dim, zVar, polys
  }, 
  {b, A} = {-1, 1}*CoefficientArrays[Transpose[(#1 == zVar & ) /@ List @@ bentSurf]];
  dim = Length[A[[1]]];
  If[ !cutZ === Infinity, 
    (* set inf-bounding level *)
    {A, b} = {Join[A, {Join[ConstantArray[0, dim - 1], {1}]}], 
      Join[b, {cutZ}]};
  ];
  {A, b}
]

pwlSurf2vertR3[Max[s__], cutZ_:10] := Module[
  {A, b}, 
  {A, b} = pwlMaxSurf2lcon[Max[s], cutZ];
  slicedPoly[lcon2vert[A, b], cutZ]
]

lcon2vert[A_, b0_] := Module[{
    (* A*x <= b *)
    m, dim, c, Dm, DmCH, k, nonsing, oneCol, bdPts, b
  }, 
  (* b might be (correctly) given as a column vector, wich confuses Thread *)
  b = Flatten[b0];
  
  (* need a feasible point to center our set *)
  {m, dim} = TensorDimensions[A];
  c = PseudoInverse[A] . b;
  If[ !VectorLess[{A . c, b}], 
    (* easy guess failed *)
    c = LinearOptimization[
      Join[ConstantArray[0, {dim}], {1}, 1], 
      {-Join[A, ConstantArray[-1, {m, 1}], 2], b}];
    Assert[Negative[c[[-1]]], 
      "Could not find feasible point!"];
    c = c[[;; -2]];
  ];
  
  (* duality normalization trick *)
  Dm = (#1/#2 & ) @@@ Transpose[{A, b - A . c}];
  
  Assert[dim == 3 || dim == 2]; (* ConvexHullMesh only works in 2d and 3d. TODO: Fix assert? *)
  DmCH = ConvexHullMesh[Dm];
  Dm = MeshCoordinates[DmCH];
  k = MeshCells[DmCH, dim - 1][[;;, 1, ;;]];
  
  (* In mathematica's general mesh framework, none of these should be singular. Not sure about qHull. *)
  nonsing = (MatrixRank[Dm[[#1, ;;]]] == dim & ) /@ k;
  oneCol = ConstantArray[1, {dim, 1}];
  bdPts = Flatten /@ DeleteDuplicates[
    (Inverse[Dm[[#1[[;; dim]], ;;]]] . oneCol + c & )
 /@ k[[Flatten[Position[nonsing, True]]]]
  ]
]

lcon2vert[A_, b_, F_, d_] := Module[{
    xp, H, vv
  }, 
  xp = PseudoInverse[F] . d;
  H = Transpose[NullSpace[F]];
  vv = lcon2vert[A . H, Flatten[b - A . xp]];
  vv . Transpose[H] + ConstantArray[Flatten[xp], Length[vv]]
]

vellHull2pwlMaxSurf[velHull_BoundaryMeshRegion, (cutZ_)?NumberQ] := Module[{
    (*
      Verison with simple cutZ.
      (0) Will need more complex version with "into-region" to avoid extra work (computing vertices going back).
      (1) fix the det[A] = 0 equation to make this more than 3D
      (2) Solve the det[A] = 0 equation smartly
      *)
    dim = RegionEmbeddingDimension[velHull], 
    verts = MeshCoordinates[velHull], 
    faces
  }, 
  faces = (verts[[#1]] & ) /@ MeshCells[velHull, dim - 1][[;;, 1, ;;]];
  faces = Select[faces, Min[N[#1[[1;;, -1]]]] < cutZ & ];
  (* extract planes in expressions of (x, y) *)
  faces = (
    SolveValues[
      Det[
        Join[{{x, y, z, 1}}, Join[#1[[;; dim]], ConstantArray[1, {dim, 1}], 2], 1]
      ] == 0, z]&
    ) /@ faces;
  (* Flatten ensures planes parallel to z are ignored, only 1 solution each otherwise *)
  Max @@ Flatten[faces]
]

vellHull2lcon[velHull_BoundaryMeshRegion, (cutZ_)?NumberQ] := Module[{
    (*
      Verison with simple cutZ.
      (0) Will need more complex version with "into-region" to avoid extra work (computing vertices going back).
      (1) fix the det[A] = 0 equation to make this more than 3D
      (2) Solve the det[A] = 0 equation smartly
      *)
    dim = RegionEmbeddingDimension[velHull], 
    verts = MeshCoordinates[velHull], 
    faces, A, b
  }, 
  faces = (verts[[#1]] & ) /@ MeshCells[velHull, dim - 1][[;;, 1, ;;]];
  faces = Select[faces, Min[N[#1[[;;, -1]]]] < cutZ & ];
  {b, A} = {-1, 1}*Normal[
    CoefficientArrays[(
        Det[Join[{{x, y, z, 1}}, Join[#1[[;; dim]], ConstantArray[1, {dim, 1}], 2], 1]] == 0 &
        ) /@ faces, {x, y, z}]];
  {A, b}
]

lcon2pwlMaxSurf[{A_, b_}] := Module[{
    (* we might want a version with explicit Zcut *)
    mZ = -A[[;;, 3]]
  }, 
  A = Transpose[Thread[A/mZ]];
  b = Thread[b/mZ];
  Max @@ (A[[;;, ;; -2]] . {x, y} - b)
]

pwlMaxSurf2vert[s_Max, cutZ_] := lcon2vert @@ pwlMaxSurf2lcon[s, cutZ]

infConv3D[s1_Max, s2_Max, cutZ_] := Module[{
    verts1 = pwlMaxSurf2vert[s1, cutZ], 
    verts2 = pwlMaxSurf2vert[s2, cutZ], 
    convHull
  }, 
  convHull = ConvexHullMesh[Flatten[Outer[Plus, verts1, verts2, 1], 1]];
  vellHull2pwlMaxSurf[convHull, cutZ]
]


meshFacesInRegion[poly_BoundaryMeshRegion, reg_ImplicitRegion] := With[{
    faces = meshFaces[poly], rDim = RegionEmbeddingDimension[reg]
  }, 
  Select[faces, AllTrue[#1, RegionMember[reg, #1[[1 ;; rDim]]] & ] & ]
]
meshFaces[(poly_BoundaryMeshRegion) | (poly_MeshRegion)] := With[{verts = MeshCoordinates[poly]}, 
  (verts[[#1]] & ) /@ MeshCells[poly, RegionEmbeddingDimension[poly] - 1][[;;, 1, ;;]]
]


(* ::Section:: *)
(*ELVIS propagation*)

PackageExport["elvisPropv1"]

elvisPropv1[gLcon1_List, gLcon2_List, yBdry_?NumericQ, Tmax_:100?NumericQ] := Module[{
    (*
      We're basically assuming gLcon1 is a global gauge and gLcon2 is a true (centered) gauge (I don't think it has to be pos. homogeneous).
      This is the sum of two epigraphs, one of the functions is basically 1D - it's the global gauge plus the inidcator of the interface.
      *)
    verts1 = lcon2vert[gLcon1[[1]], gLcon1[[2]]], 
    verts2 = lcon2vert[gLcon2[[1]], gLcon2[[2]]], 
    F = {{0, 1, 0}}, d = {{yBdry}}, 
    vSlice, velEpiFwd, velEpiBwd
  }, 
  vSlice = lcon2vert[gLcon1[[1]], gLcon1[[2]], F, d];
  velEpiFwd = ConvexHullMesh[
    Flatten[Outer[Plus, vSlice, verts2, 1], 1]
  ];
  velEpiBwd = ConvexHullMesh[
    Flatten[Outer[Plus, verts1, MeshCoordinates[velEpiFwd], 1], 1]
  ];
  (* Fwd, Bwd*)
  {Piecewise[{{vellHull2pwlMaxSurf[velEpiFwd, Tmax], y >= yBdry}}, 0], Piecewise[{{vellHull2pwlMaxSurf[velEpiBwd, Tmax], y <= yBdry}}, 0]}
]