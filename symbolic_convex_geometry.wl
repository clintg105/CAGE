(* ::Package:: *)

(* ::Input::Initialization:: *)
On[Assert];


(* ::Input::Initialization:: *)
trep[expr_,vars_,inp_]:=expr/.Thread[vars->inp]
mtrep[expr_,vars_,inp_]:=expr/.Thread[vars->#]&/@inp


(* ::Input::Initialization:: *)
(* useres should avoid custom specifcation of \[FormalX], \[FormalS], and \[FormalZeta] do to use in codebase (as well as \[FormalL], due to use as generic symbol)*)
formalScalar=\[FormalX];

formalVector[n_Integer]:=Array[Subscript[formalScalar,#]&,n]
formalVector[n_Integer,m_]:=Array[Superscript[Subscript[formalScalar,#],m]&,n]
formalVector[n_List,varargin___]:=With[{x=formalVector[Length[n],varargin]},If[SameQ[n,x],x/.formalScalar->\[FormalY],x]]

formalVectors[n_,m_]:=formalVector[n,#]&/@Range[m]

formalParameter[varargin___]:=formalVector[varargin]/.formalScalar->\[FormalS]
formalCovector[varargin___]:=formalVector[varargin]/.formalScalar->\[FormalZeta]


(* ::Input:: *)
(*Solve[formalVector[3,1]==3formalVector[3,2],Evaluate[formalVector[3,2]]]*)


(* ::Input::Initialization:: *)
repelem[ix_List]:=Flatten[ConstantArray[#1,#2]&@@@Transpose@{Range[Length[ix]],ix}]
repelem[v_List,ix_List]:=v[[repelem[ix]]]


(* ::Input:: *)
(*repelem[{a,b,c},{3,4,8}]*)


(* ::Input::Initialization:: *)
cyclicTakeUpTo[v_List,n_Integer]:=v[[Mod[Range[n]-1,Length[v]]+1]]


(* ::Input::Initialization:: *)
(* https://mathematica.stackexchange.com/questions/54486/how-to-access-new-colour-schemes-in-version-10 *)
showDiscreteColorThemes[]:=Grid[{#,getDiscreteColorTheme[#]}&/@("Color"/. Charting`$PlotThemes),Dividers->All]
getDiscreteColorTheme[name_]:=Cases["DefaultPlotStyle"/.(Method/.Charting`ResolvePlotTheme[name,ListPlot]),_RGBColor,Infinity]


(* ::Input::Initialization:: *)
pwGetPairs[f_Piecewise]:=Module[{vals,cnds},
vals=Append[f[[1,;;,1]],f[[2]]];
cnds=f[[1,;;,2]];
cnds=Append[cnds,Not@Fold[Or,cnds]];
{vals,cnds}]
pwAddConditionIgnoreLast[f_Piecewise,cnd_]:=Module[{},
f[[1,;;,2]]=#&&cnd&/@f[[1,;;,2]];f
]
pwAddCondition[f_Piecewise,cnd_]:=Module[{vals,cnds},
{vals,cnds}=pwGetPairs[f];
cnds=(#&&cnd&)/@cnds;
Piecewise[{vals,cnds}\[Transpose],Undefined[]]
]


(* ::Input::Initialization:: *)
(*TODO: pwDropLastSafe *)
pwDropLast[f_Piecewise]:=f/.Piecewise->\[FormalL]//.\[FormalL][a_List,b_]:>Piecewise[a[[1;;-2]],a[[-1,1]]]


(* ::Input::Initialization:: *)
forceString[x_]:=If[Head@x===String,x,ToString[x]]


(* ::Input::Initialization:: *)
Clear[cvxReduce]
cvxReduceCrawler[f_[a___]]:=f@@(cvxReduce/@{a})
cvxReduceCrawler[a_Symbol]:=a
cvxReduceCrawler[a_?NumberQ]:=a
cvxReduceCrawler[indicator[cnd_]]:=Piecewise[{{0,cnd}},Infinity]
cvxReduce[x_]:=cvxReduceCrawler[x]//PiecewiseExpand


(* ::Input:: *)
(*Piecewise[{{a,b>0},{b,a>0}},0]+indicator[b>0]//cvxReduce*)


(* ::Input:: *)
(*cvxReduce[x^2+y^2<=a]*)


(* ::Input::Initialization:: *)
cvxResolveOverReals[f_[a___],s___]:=f@@(cvxResolveOverReals[#,s]&/@{a})
cvxResolveOverReals[a_Symbol,___]:=a
cvxResolveOverReals[a_?NumberQ,___]:=a

(* level set of 1 anyway, common case mathematica misses *)
cvxResolveOverReals[Power[expr_,1/2]<=1,vars_,cnd_]:=If[
Simplify[expr>=0,cnd]===True||FullSimplify[Reduce[expr>=0&&Im[Alternatives@@vars]==0,Complexes],cnd]===True,
cvxResolveOverReals[expr,vars,cnd]<=1,Power[cvxResolveOverReals[expr,vars,cnd],1/2]<=1
]

cvxResolveOverReals[a_+indicator[b_],vars_,cnd_]:=cvxResolveOverReals[a,vars,cnd&&b]+indicator[b]


cvxResolveOverReals[Max[a_,b_],vars_,cnd_]:=Which[
FullSimplify[Reduce[a>=b&&Im[Alternatives@@vars]==0,Complexes],cnd]===True,a,
FullSimplify[Reduce[a<=b&&Im[Alternatives@@vars]==0,Complexes],cnd]===True,b,
True,Max@@(cvxResolveOverReals[#,vars,cnd]&/@{a,b})
]
cvxResolveOverReals[Min[a_,b_],vars_,cnd_]:=Which[
FullSimplify[Reduce[a<=b&&Im[Alternatives@@vars]==0,Complexes],cnd]===True,a,
FullSimplify[Reduce[a>=b&&Im[Alternatives@@vars]==0,Complexes],cnd]===True,b,
True,Max@@(cvxResolveOverReals[#,vars,cnd]&/@{a,b})
]
(* This old way breaks: f=initializeSet[{ x, y}.{ x,y}<=1/.Thread[{x,y}->{x,y}+1],{x,y}]
f["polar"]["polar"]*)


(* ::Input:: *)
(*cvxResolveOverReals[Max[-x-Sqrt[2] Sqrt[x] Sqrt[y]-y,-x+Sqrt[2] Sqrt[x] Sqrt[y]-y],{x,y},x<=0&&y<=0]//RepeatedTiming*)


(* ::Subsection:: *)
(*Indicator Functions*)


(* ::Input::Initialization:: *)
MakeBoxes[closedIntervalBracket[x__],fmt:TraditionalForm]^:=RowBox[{"[",RowBox[Riffle[BoxForm`ListMakeBoxes[{x},fmt],","]],"]"}]

Format[ind[fx_,x_,{a_,b_}],TraditionalForm]:=Subscript[\[Delta], x \[Element] closedIntervalBracket[a,b]][fx]
Format[ind[x_,x_,{a_,b_}],TraditionalForm]:=Subscript[\[Delta], closedIntervalBracket[a,b]][x]
Format[indicator[x_],TraditionalForm]:=Subscript[\[Delta], closedIntervalBracket[x]]


(* ::Input:: *)
(**)


(* ::Input::Initialization:: *)
MakeBoxes[closedIntervalBracket[x__],fmt:TraditionalForm]^:=RowBox[{"[",RowBox[Riffle[BoxForm`ListMakeBoxes[{x},fmt],","]],"]"}]

Format[ind[fx_,x_,{a_,b_}],TraditionalForm]:=Subscript[\[Delta], x \[Element] closedIntervalBracket[a,b]][fx]
Format[ind[x_,x_,{a_,b_}],TraditionalForm]:=Subscript[\[Delta], closedIntervalBracket[a,b]][x]


(* ::Input:: *)
(*fun[b+a_.]:=a*)


(* ::Input:: *)
(*fun[b+1]*)


(* ::Input:: *)
(*fun[b]*)


(* ::Input::Initialization:: *)
ind[\[Lambda]_. fz_+\[Delta]_.,z_Symbol,{a_,b_}]/;
!And[\[Lambda]===1,\[Delta]===0]&&!FreeQ[fz,z]:=
ind[fz,z,{( a-\[Delta])/\[Lambda],( b-\[Delta])/\[Lambda]}]


(* ::Input:: *)
(*ind[7x^2+b,x,{-1,1}]*)
(*%//TraditionalForm*)


(* ::Input::Initialization:: *)
SetAttributes[ind,HoldFirst](* this is only so g can be Sqrt *)
ind[g_[fz_],z_Symbol,{a_,b_}]/;
!FreeQ[fz,z]&&
(If[FunctionInjective[g[fz],z,PerformanceGoal->"Speed"]===True,True,
FunctionInjective[{g[fz],a<z<b},z,PerformanceGoal->"Speed"]]):=
Module[{gi=InverseFunction[g[#]&],bnds,fm},
(* TODO: Faster methods in other (not purely symbolic) cases *)
fm=FunctionMonotonicity[g[z],z,PerformanceGoal->"Speed"];
If[SameQ[Head@fm,ConditionalExpression],
fm=fm[[1]]];(* TODO: Context tracking *)
Switch[fm,
1,ind[fz,z,{gi[a],gi[b]}],
0,{Indeterminate,"ind with constant mapping"},
-1,ind[fz,z,{gi[b],gi[a]}],
Indeterminate,bnds={gi[b],gi[a]};ind[fz,z,{Min@@bnds,Max@@bnds}]
]
]


(* ::Input:: *)
(*SetAttributes[ind2,HoldFirst]*)
(*ind2[g_[fz_],z_Symbol,{a_,b_}]:=If[FunctionInjective[g[fz],z,PerformanceGoal->"Speed"]===True,True,*)
(*FunctionInjective[{g[fz],a<z<b},z,PerformanceGoal->"Speed"]]*)


(* ::Input:: *)
(*ind[4Log[4z+5]+8,z,{-1,1}]*)
(*ind[4Log[4z+5]+8,z,m{-1,1}+b]*)
(*ind[z^2,z,{3,8}]*)


(* ::Input:: *)
(*FunctionInjective[{z^2,3<z<8},z,PerformanceGoal->"Speed"]*)


(* ::Input:: *)
(**)


(* ::Subsection:: *)
(*Algebra Tools*)


(* ::Input:: *)
(*isLinearIn[expr_,var_Symbol]:=*)


(* ::Subsection:: *)
(*Implicit Region Tests*)


(* ::Input::Initialization:: *)
zeroSymmetric[cons_LessEqual,vars_]:=Reduce[ForAll[vars,
Implies[cons,trep[cons,vars,-vars]]],
vars,Reals]
bounded[cons_,vars_]:=Resolve[Exists[\[FormalL],ForAll[Evaluate[vars],cons,vars . vars<=\[FormalL]]]]


(* ::Input:: *)
(*zeroSymmetric[{x,y} . {x,y}<=3,{x,y}]*)


(* ::Input:: *)
(*bounded[{x,y} . {x,y}<=3,{x,y}]*)


(* ::Input:: *)
(**)


(* ::Subsection:: *)
(*Implicit Region > Implicit Region Transforms*)


(* ::Input::Initialization:: *)
polar[expr_,vars_]:=Module[{newVars=formalCovector[vars],pCnd},
pCnd=ForAll[Evaluate[newVars],trep[expr,vars,newVars],vars . newVars<=1];
{Reduce[pCnd,newVars,Reals],vars}]


(* ::Input::Initialization:: *)
recc[expr_,vars_]:=Module[{newVars=formalCovector[vars],reccCnd},
reccCnd=ForAll[Evaluate[newVars],trep[expr,vars,newVars],trep[expr,vars,newVars+vars]];
{Reduce[reccCnd,newVars,Reals],vars}]
polarRecc[expr_,vars_]:=polar@@recc[expr,vars]


(* ::Subsection:: *)
(*Implicit Region > Function Transforms*)


(* ::Input::Initialization:: *)
support[expr_,vars_]:=With[{newVars=formalVector[vars]},
Maximize[{vars . newVars,trep[expr,vars,newVars]},newVars,Reals][[1]]
]


(* ::Subsection:: *)
(*Function Tests*)


(* ::Input::Initialization:: *)
convex[expr_,vars_]:=Module[{x=formalVectors[vars,2],c={\[FormalL],1-\[FormalL]}},
(* this is amlos never used in favor of FunctionComplexity *)
Reduce[ForAll[Evaluate[Append[vars,\[FormalL]]],0<\[FormalL]<1,
trep[expr,vars,c . x]<=c . mtrep[expr,vars,x]],
vars,Reals]
]
positiveHomogeneous[expr_,vars_]:=Reduce[ForAll[Evaluate[Append[vars,\[FormalL]]],\[FormalL]>0,
\[FormalL] expr==trep[expr,vars,\[FormalL] vars]],
vars,Reals]
(* sublinear - Great example: when working with classes, dfn 3.3.1 or prop 3.3.2 can be used *)
sublinear[expr_,vars_]:=Module[{x=formalVectors[vars,2],l=formalParameter[2]},
Reduce[ForAll[Evaluate[Flatten[Join[x,l]]],Fold[And,#>0&/@l],
trep[expr,vars,l . x]==l . mtrep[expr,vars,x]],
vars,Reals]
]


(* ::Input:: *)
(*positiveHomogeneous[ #,{x,y}]&/@{x^2+y^2,Sqrt[a x^2+y^2]}*)


(* ::Input:: *)
(*convex[ #,{x,y}]&/@{x^2+y^2,Sqrt[a x^2+y^2]}(* the second one taks forever, wold be good to speed test with c1 / c2 convex*)*)


(* ::Input:: *)
(*Clear[x]*)


(* ::Input:: *)
(*sublinear[ #,{x,y}]&/@{x^2+y^2,Sqrt[a x^2+y^2]}*)


(* ::Subsection:: *)
(*Function Transforms*)


(* ::Input::Initialization:: *)
epi[expr_,vars_]:=With[{x=formalVector[Length[vars]+1]},{trep[expr,vars,x[[;;-2]]]<=x[[-1]],x}]
(*lev[expr_,vars_,alpha_:1]:={expr<=alpha,vars}
dom[expr_,vars_]:={expr<Infinity,vars}*)


(* ::Input:: *)
(*epi[x^2+y^2,{x,y},cvxReduce]*)


(* ::Input::Initialization:: *)
Clear[dom,lev]
dom[Plus[expr_,indicator[cnd_]],vars_]:=dom[{expr,cnd},vars]
dom[{Plus[expr_,indicator[cnd_]],cnd0_},vars_]:=dom[{expr,cnd&&cnd0},vars]

dom[expr_,vars_]:=dom[{expr,True},vars]
dom[{expr_,cnd_},vars_]:={Reduce[expr<Infinity&&cnd,vars,Reals],vars}

lev[expr_,vars_,alpha_:1]:=lev[{expr/.indicator[_]->0,dom[expr,vars][[1]]},vars,alpha]
lev[{expr_,cnd_},vars_,alpha_:1]:={expr<=alpha&&cnd&&dom[expr,vars][[1]],vars}


(* ::Input:: *)
(*lev[{x,y} . {x,y}+indicator[x<1],{x,y}]*)


(* ::Input::Initialization:: *)
(*cvxReduce[{expr_,True}]:=expr
cvxReduce[expr_:Except[_List]]:=cvxReduce[{expr,True}]
cvxReduce[expr_Plus]:=cvxReduce[{expr,True}]
cvxReduce[{expr_,cnd_}]:=Piecewise[{{cvxReduce[expr],cnd}},Indeterminate]
cvxReduce[{Plus[expr_,indicator[cndi_]],cnd_}]:=Piecewise[{{cvxReduce[expr],cndi&&cnd//Reduce},{Infinity,!cndi&&cnd//Reduce}},Indeterminate]
cvxReduce[Plus[expr_,indicator[cndi_]]]:=Piecewise[{{cvxReduce[expr],cndi}},Infinity]
cvxReduce[LessEqual[a_,b_]]:=LessEqual[cvxReduce[a],cvxReduce[b]]*)


(* ::Input:: *)
(*cvxReduce[{a x+indicator[x<1],a>0}]*)
(*cvxReduce[a x+indicator[x<1]+indicator[x>-9]]//PiecewiseExpand*)


(* ::Input:: *)
(*cvxReduce[a x+7indicator[x<1]+indicator[x>-9]]*)


(* ::Input:: *)
(*dom[x+indicator[x<1]+indicator[x>-8],{x,y}]*)


(* ::Input:: *)
(**)


(* ::Input:: *)
(*lev[Plus[expr_,indicator[cnd_]],vars_,alpha_:1]:={expr<=alpha,vars}*)


(* ::Input::Initialization:: *)
subgradient[expr_,vars_]:=Module[{x=vars,y=formalVector[vars],z=formalCovector[vars]},
Reduce[ForAll[y,
(y-x) . z<=trep[expr,vars,y]-trep[expr,vars,x]],
z,Reals]
]


(* ::Input:: *)
(*subgradient[Abs[x],{x}]*)
(*subgradient[Max[x/2,x^2],{x}]*)


(* ::Input:: *)
(*reduceParametricPieces[BooleanConvert[subgradient[Max[x/2,x^2],{x}],"DNF"],{x}]//MatrixForm*)


(* ::Input:: *)
(*Reduce[(x<0&&Subscript[\[FormalZeta], 1]==-1)||(x==0&&-1<=Subscript[\[FormalZeta], 1]<=1)||(x>0&&Subscript[\[FormalZeta], 1]==1),{x}]*)


(* ::Input::Initialization:: *)
subgradientPiecewiseMultiValued[expr_,vars_]:=With[{pVars=formalCovector[vars],sg=subgradient[expr,vars]},mapPiecewiseValues[Switch[#,
_Integer,#,(* catches Piecewise default zero case *)
_Equal,With[{f=Flatten[pVars/.{ToRules[#]}]},If[Length[f]==1,f[[1]],ImplicitRegion[#,Evaluate[pVars]]]],
_,ImplicitRegion[#,Evaluate[pVars]]
]&,nestedPiecewiseFromHierarchicalLogic[sg,pVars]]]


(* ::Input:: *)
(*subgradientPiecewiseMultiValued[Max[x/2,x^2],{x}]*)


(* ::Input::Initialization:: *)
c1SubgradientR1[f_,{var_}]:=Module[{deriv,disc,points},
(* does not check jump discontinuities! *)
(* Convex 1-var *)
deriv=D[f,var];
(*Find the points of discontinuity*)
disc=FunctionDiscontinuities[deriv,var];
(*Find the actual points where discontinuity occurs*)
points=SolveValues[disc,var];
(*Glue the derivative together at points of discontinuity*)
PiecewiseExpand@Piecewise[
(*For each point of discontinuity,form an interval*)
Append[{
Interval[{
Limit[deriv,var->#,Direction->"FromAbove"],Limit[deriv,var->#,Direction->"FromBelow"]
}],
var==#
}&/@points,
(*For other points,simply use the derivative*)
{deriv,True}]
]
]


(* ::Input:: *)
(*f=Piecewise[{{x,0<x<1},{2*x-1,x>=1},{-x,x<=0}},0];*)
(*Plot[f,{x,-1,2}]*)
(*RepeatedTiming[c1SubgradientR1[f,{x}],1]*)
(*RepeatedTiming[sg=subgradientPiecewiseMultiValued[f,{x}],1]*)


(* ::Input::Initialization:: *)
ClearAll[solvePiecewise]
toRegion[f_]:=Module[{f0=f,ir},
(* Reduces pwmv function with 'Interval' and dervied ImplicitRegions to one with just ImplicitRegions. *)
(* Do reduction of ImplicitRegion *)
f0=f0/.ImplicitRegion->ir;
f0=f0//.{
Interval[{a_,b_}]:>ir[a<=y<=b,{y}],
ir[fxy_,{y_}]+fx_:> ir[fxy/.y->y-fx,{y}]
};
f0=f0/.ir->ImplicitRegion;
(* Return reduced function *)
f0
];
solvePiecewise[eq_,var_]:=Module[
{lhs,rhs,rel,pieces,regionPieces,nonRegionPieces,regionSolutions,nonRegionSolutions,solutions},
(*TODO: Fix lhs needing to be equation *)
(*Get left hand side and right hand side of the equation*)
If[Head[eq]===Equal,
{lhs,rhs}=List@@eq;
rel=Equal,
lhs=eq[[1]];
rhs=eq[[2]];
rel=Head[eq]];
lhs=toRegion[lhs];
(*Get piecewise pieces*)
pieces=Transpose@pwGetPairs[lhs];
(*Separate region pieces and non-region pieces*)
regionPieces=Select[pieces,Head[#[[1]]]===ImplicitRegion&];
nonRegionPieces=Select[pieces,Head[#[[1]]]=!=ImplicitRegion&];
(*Process each region piece*)
regionSolutions=(r|->Element[rhs,r[[1]]]&&r[[2]])/@regionPieces;
(*Echo[regionPieces//MatrixForm];*)
(*Echo[{regionPieces,Reduce[Or@@regionSolutions,var,Reals],ImplicitRegion[Reduce[Or@@regionSolutions,var,Reals],var]}];*)
(*Process each non-region piece*)
nonRegionSolutions=(expr|->rel[expr[[1]],rhs]&&expr[[2]])/@nonRegionPieces;
(*Echo[Reduce[Or@@nonRegionSolutions,var,Reals]];*)
(*Join all solutions*)
solutions=Join[regionSolutions,nonRegionSolutions];
(*Create final implicit region*)
ImplicitRegion[Reduce[Or@@solutions,var,Reals],var]]


(* ::Input:: *)
(*sg=c1SubgradientR1[Piecewise[{{x,0<x<1},{2*x-1,x>=1},{-x,x<=0}},0],{x}]*)
(*solvePiecewise[sg<={0},{x}]*)


(* ::Input:: *)
(*Plot3D[Abs[x]+Abs[y],{x,-1,1},{y,-1,1}]*)


(* ::Input:: *)
(*nestedPiecewiseFromHierarchicalLogic[sg0,formalCovector[2]]*)


(* ::Input:: *)
(*sg0=subgradient[Abs[x]+Abs[y],{x,y}]*)


(* ::Input:: *)
(*sg=subgradientPiecewiseMultiValued[Abs[x]+Abs[y],{x,y}]*)


(* ::Input:: *)
(*solvePiecewise[sg=={0,0},{x,y}]*)
(**)
(*RegionPlot[3 y<=x<y||(y==0&&x==0),{x,-1,1},{y,-1,1}]*)


(* ::Input:: *)
(*!((x < 0 && x - y > 0) || (x < 0 && x - y == 0) || (x < 0 && x - y < *)
(*    0 && y < 0) || (x < 0 && y == 0) || x < 0 || (x == 0 && y == 0) || (x*)
(*     == 0 && y < 0) || x == 0 || y < 0 || y == 0 || (y > 0 && x - y > 0) *)
(*    || x - y == 0) // Reduce*)


(* ::Input:: *)
(*sg=subgradientPiecewiseMultiValued[Abs[x]+Abs[y],{x,y}]//pwDropLast//PiecewiseExpand*)
(*solvePiecewise[sg=={0,0},{x,y}]*)
(*RegionPlot[3 y<=x<y||(y==0&&x==0),{x,-1,1},{y,-1,1}]*)
(*(* I blame PiecewiseExpand*)*)


(* ::Subsection:: *)
(*parametricPiece*)


(* ::Input::Initialization:: *)
toInequality[p_]:=p/.{
Less[a_,b_,c_]:>Inequality[a,Less,b,Less,c],
LessEqual[a_,b_,c_]:>Inequality[a,LessEqual,b,LessEqual,c],
(* assuming the variable of interest is always on the left (based on reduce) *)
Less[a_,b_]:>Inequality[-Infinity,Less,a,Less,b],
LessEqual[a_,b_]:>Inequality[-Infinity,Less,a,LessEqual,b],
Greater[a_,b_]:>Inequality[b,LessEqual,a,Less,Infinity],
GreaterEqual[a_,b_]:>Inequality[b,Less,a,Less,Infinity]};
toInequalityLeftBiasedToCenter=toInequality;


(* ::Input:: *)
(*vars = {x, y, z}*)
(**)
(*bounds = {{-x y, x y}, {0, 1}, {y, y}}*)


(* ::Input::Initialization:: *)
(* for ordering generation for-loops, like in ParametricPlot *)
varUsageOrdering[exprs_,vars_]:=OrderingBy[Transpose[{vars,exprs}],!FreeQ[#[[2]],#[[1]]]&]


(* ::Input:: *)
(*{vars,exprs}={{y,x},{{-(1/2) Sqrt[3+4 x-4 x^2],-(1/2) Sqrt[3+4 x-8 x^2]},{1/16 (5-Sqrt[119]),1/24 (5-Sqrt[166])}}}*)
(*OrderingBy[Transpose[{vars,exprs}],!FreeQ[#[[2]],#[[1]]]&]*)
(*{vars,exprs}={{x,y},{{0,1/24 (-3+5 Sqrt[6])},{-(1/2) Sqrt[3-4 x-4 x^2],-(1/2) Sqrt[3-4 x-8 x^2]}}}*)
(*OrderingBy[Transpose[{vars,exprs}],!FreeQ[#[[2]],#[[1]]]&]*)


(* ::Input:: *)
(*exprs*)


(* ::Input:: *)
(*FreeQ[{-(1/2) Sqrt[3-4 x-4 x^2],-(1/2) Sqrt[3-4 x-8 x^2]},x]*)


(* ::Input:: *)
(*exprs*)


(* ::Input:: *)
(*Outer[!FreeQ[#2,#1]&,vars,exprs]*)
(*AdjacencyGraph[Boole[%]]*)
(*DepthFirstScan[%]*)


(* ::Input::Initialization:: *)
sortedSubsetIndices[subset_,superset_]:=With[
(* things not in superset go at end *)
{orderInBigList=Flatten[Position[superset,#]&/@subset/.{}->Infinity]},
Ordering[orderInBigList,All,LessEqual]
]


(* ::Input::Initialization:: *)
reduceParametricPiece[p_,vars_:{}]:=Module[{(*pSplit,pHeads,eqIxs,mixedInEqIxs,constIxs,pOut*)},
(* reduce each parametric peice into a list: {{f[x],g[y],h[z]}, {x,y}, {{x0,x1},{y0,y1}}}, that is, {[Parametric Equations], [Parametric Variables], [Parametric Bounds]}*)
pSplit=p/.And->List//toInequality;
pHeads=Head/@pSplit;
eqIxs=Flatten@Position[pHeads,Equal];
mixedInEqIxs=Flatten@Position[pHeads,Inequality];
Assert[Length[Join[eqIxs,mixedInEqIxs]]==Length[p]];
If[Length[mixedInEqIxs]==0,
pOut={First[vars//.{ToRules[p]}],{},{}},
pOut={If[eqIxs==={},vars,First[vars//.{ToRules[Fold[And,pSplit[[eqIxs]]]]}]],pSplit[[mixedInEqIxs]][[;;,3]],Transpose@{pSplit[[mixedInEqIxs]][[;;,1]],pSplit[[mixedInEqIxs]][[;;,5]]}};
];
constIxs=Flatten@Position[MemberQ[pOut[[2]],#]&/@vars,False,1];
pOut[[1]]=pOut[[1]]/.Thread[vars[[constIxs]]->pOut[[1]][[constIxs]]];
(*pOut[[3]]=pOut[[3]]/.Thread[vars[[constIxs]]->pOut[[1]][[constIxs]]];*)
pOut
]
reduceParametricPieces[p_,vars_]:=If[Head[p]===Or,reduceParametricPiece[#,vars]&/@List@@p,{reduceParametricPiece[p,vars]}]


(* ::Input::Initialization:: *)
plotParamPiece[p_,vars_,varagin___]:=Module[{constIxs,ordering},If[Length[p[[1]]]==2,
If[p[[2]]==={},
Graphics[Point[p[[1]]]],
constIxs=Flatten@Position[MemberQ[p[[2]],#]&/@vars,False,1];
ordering=varUsageOrdering[p[[3]],p[[2]]];
ParametricPlot[p[[1]]/.Thread[vars[[constIxs]]->p[[1]][[constIxs]]],Evaluate[Sequence@@((Transpose@Join[{p[[2]][[ordering]]},Transpose@p[[3]][[ordering]]])/.{{x_,-Infinity,b_}:>{x,(b-1),b},{x_,b_,Infinity}:>{x,b,(b+1)}})],varagin]
],
If[p[[2]]==={},
Graphics3D[Point[p[[1]]]],
constIxs=Flatten@Position[MemberQ[p[[2]],#]&/@vars,False,1];
ordering=varUsageOrdering[p[[3]],p[[2]]];
ParametricPlot3D[p[[1]]/.Thread[vars[[constIxs]]->p[[1]][[constIxs]]],Evaluate[Sequence@@((Transpose@Join[{p[[2]][[ordering]]},Transpose@(p[[3]][[ordering]]//N//Re)])/.{{x_,-Infinity,b_}:>{x,(b-1),b},{x_,b_,Infinity}:>{x,b,(b+1)}})],varagin]
]
]]


(* ::Input:: *)
(*cnd=({x,y,z} . {x,y,z}<=1/.x->x-1/2)&&({x,y,z} . {x,y,z}<=1/.x->x+1/2)&&({x,y,z} . {x,y,z}<=1/.z->z+1/2)&&({x,y,z} . {x,y,z}<=1/.z->z-1/2)(*&&x+y+z<=1/4*)*)
(*vars={x,y,z}*)
(*atlas=boundaryAtlas[cnd,vars];*)
(*testPoint=First[vars/.FindInstance[atlas[[5,atlasCol["simpleCnd"]]],vars]]*)
(*boundaryAtlasLookup[atlas,vars,testPoint]*)
(*boundaryAtlasPlot[atlas,vars]*)
(**)


(* ::Input::Initialization:: *)
piecewiseNestedQ[expr_]:=Length[Position[expr,Piecewise]]>1
piecewiseValueWrapper[expr_Piecewise]:=Piecewise[{piecewiseValueWrapper[#1],#2}&@@@#1,piecewiseValueWrapper[#2]]&@@expr
mapPiecewiseValues[fun_,expr_]:=piecewiseValueWrapper[expr]/.piecewiseValueWrapper->fun


(* ::Input:: *)
(*pVars=formalCovector[1];*)
(*pw=nestedPiecewiseFromHierarchicalLogic[sg,pVars]*)
(*mapPiecewiseValues[Switch[#,*)
(*_Integer,#,(* catches Piecewise default zero case *)*)
(*_Equal,With[{f=Flatten[pVars/.{ToRules[#]}]},If[Length[f]==1,f[[1]],f]],*)
(*_,ImplicitRegion[#,Evaluate[pVars]]*)
(*]&,pw]*)
(*%/.x->1/2*)


(* ::Input:: *)
(*sg=subgradient[Abs[x]+Abs[y],{x,y}];*)
(*pw=nestedPiecewiseFromHierarchicalLogic[sg,formalCovector[2]];*)


(* ::Input:: *)
(*headMapLowest[fun_,expr_]:=Module[{lowestPositions=MaximalBy[Position[pw,Piecewise],Length]},]*)


(* ::Input:: *)
(*MaximalBy[Position[pw,Piecewise],Length]*)


(* ::Input::Initialization:: *)
nestedPiecewiseFromHierarchicalLogic[expr_,pVars_]:=Block[{exprPairedCndVal},
(* Assumes expr is "Tree-Like" with pVars at the lowest level. Example: 
nestedPiecewiseFromHierarchicalLogic[
(x>=0 && ((y>=0 && (z==x)) || (y<0 && (z==y)))) || (x<0 && (x<z<y)),
z] *)
(* pVars are parametric vars, these are the the variables that are NOT part of the Piecewise conditions *)
exprPairedCndVal=expr//.And[cnd_?(FreeQ[#,Alternatives@@pVars]&),val_]:>{val,cnd};
(* there is some porperty of the operator Or that makes it have to be spoofed (or else it stays persistent as Head) *)
exprPairedCndVal/.Or->\[FormalL]//.\[FormalL][x___List]:>Piecewise[{x}]/.\[FormalL]->Or
]


(* ::Input:: *)
(*sg=subgradient[Max[x/2,x^2],{x}]*)
(*nestedPiecewiseFromHierarchicalLogic[sg,formalCovector[2]]*)


(* ::Input:: *)
(*sg=subgradient[Abs[x]+Abs[y],{x,y}];*)
(*nestedPiecewiseFromHierarchicalLogic[sg,formalCovector[2]]*)


(* ::Subsection:: *)
(*HalfSpaces*)


(* ::Input::Initialization:: *)
int[R_]:=RegionDifference[R,RegionBoundary[R]]
originRegion[n_]:=ImplicitRegion[x==Table[0,n],x]


(* ::Input::Initialization:: *)
orthCompAff[AffineSpace[points_List]]:=Module[
(* The complement returned here will intersect the AffineSpace at the first point provided in it's definition. Not sure of rigor here...

Issues: This definition is "numeric" over the points due to the usage of Select and Orthogonalize.*)
{R=AffineSpace[points],p0=points[[1]],pCen,pCenOrth},
pCen=Table[p-p0,{p,points}];
pCenOrth=Select[Orthogonalize[pCen~Join~IdentityMatrix[RegionEmbeddingDimension[R]]],Norm[#]>0&][[Length[points];;]];
AffineSpace[{p0}~Join~Table[p+p0,{p,pCenOrth}]]
]
orthCompAff[AffineSpace[points_List],center_]:=TransformedRegion[
orthCompAff[AffineSpace[points]],
TranslationTransform[-points[[1]]+center]]


(* ::Input:: *)
(*R=AffineSpace[{{0,1,0},{0,0,0},{0,0,1}}];*)
(*Show[Graphics3D[{Orange,R,Blue,orthCompAff[R],Point[R[[1,1]]]}]]*)


(* ::Input::Initialization:: *)
ray[origin_,direction_]:=ConicHullRegion[{origin},{direction}]


(* ::Input:: *)
(*Graphics@ConicHullRegion[{{0,0}},{{1,1}}]*)


(* ::Subsection:: *)
(*lagrangeStationaryPoints*)


(* ::Input::Initialization:: *)
(* find solutions to Subscript[inf, cons] expr if exper is convex *)
lagrangeStationaryPoints[expr_,cons_Equal,vars_List]:=expr/. Solve[Eliminate[D[expr-\[Lambda] (cons[[2]]-cons[[1]]),{Join[vars,{\[Lambda]}]}]==0,\[Lambda]],vars]


(* ::Subsection:: *)
(*polarGenerators[pts_] (Discrete)*)


(* ::Input:: *)
(*<<"https://gist.githubusercontent.com/jasondbiggs/c3d9410af3195da514a442be5b563ab8/raw/80ac5074077f0d4b1366540c8c710e35cb530ddd/NDConvexHull.m"*)
(*(* https://mathematica.stackexchange.com/questions/113492/how-to-generate-higher-dimensional-convex-hull *)*)
(*CHNQuickHull[{{0,0,1},{1,2,1},{1,1,1},{6,9,1}}]*)


(* ::Subsection:: *)
(*Conic Hull (Implicit)*)


(* ::Input::Initialization:: *)
toLevelRegion[ImplicitRegion[expr_LessEqual,vars_]]:=levelRegion[expr[[1]]-expr[[2]]+1,vars]
(* implicit regions don't get wrapped until later, when we are going class mode *)

conicHull2[expr_,vars_]:=Module[{dim=Length[vars],g=Grad[expr[[1]],vars]},
(* slightly fancy version *)
(* assumes convexity *)
If[dim==2,
ConicHullRegion[{{0,0}},SolveValues[vars . g==0&&(expr/.LessEqual->Equal),vars]],
ImplicitRegion[Reduce[vars . g==0&&expr,vars,Reals],vars]
]
]

conicHull[expr_,vars_]:=Module[{dim=Length[vars],g=Grad[expr[[1]],vars]},
(* assumes convexity *)
{Reduce[vars . g==0&&expr,vars,Reals],vars}
]


(* ::Input:: *)
(*expr=(x-1)^2-y+2<=1*)
(*vars={x,y};*)
(*conicHull[expr,vars]*)


(* ::Input:: *)
(*dim=Length[vars]*)
(*g=Grad[expr[[1]],vars]*)
(*(* assumes convexity *)*)
(*If[dim==2,*)
(*ConicHullRegion[{{0,0}},SolveValues[Reduce[vars . g==0&&(expr/.LessEqual->Equal),vars,Reals],vars]],*)
(*ImplicitRegion[Reduce[vars . g==0&&expr,vars,Reals],vars]*)
(*]*)
(*g/.Thread[{x,y}->Transpose[{{-(Sqrt[3]/2),3/2},{Sqrt[3]/2,3/2}}]]*)
(*Graphics[{conicHull[expr,vars],ConicHullRegion[{{0,0}},Transpose@{{-Sqrt[3],Sqrt[3]},{-1,-1}}]}]*)


(* ::Input:: *)
(*expr=({x,y} . {x,y}<=1/.y->y-2)*)
(*vars={x,y};*)
(*RegionConvert[conicHull[expr,vars],"Implicit"]*)


(* ::Subsection:: *)
(*Active region (Intersection with parametric conic hull)*)


(* ::Input:: *)
(*impl={x,y,z} . {x,y,z}<=1/.x->x-3*)
(*f=impl[[1]]-impl[[2]]*)
(*0<={x,y,z} . Grad[f,{x,y,z}]&&(impl/.LessEqual->Equal)*)
(*BooleanConvert[Reduce[%,{x,y,z},Reals],"DNF"]*)


(* ::Subsection:: *)
(*polarParameterization*)


(* ::Input::Initialization:: *)
polarParameterization[param_,vars_]:=Module[{n=Length[param],grad=Transpose[Grad[param,vars]],
e,M},
M=Transpose[{
Array[Subscript[e, #]&,n+1],
param~Join~{1},
Sequence@@Join[
Array[grad[[##]]&,{n-1,n}],
ConstantArray[{0},n-1]
,2]
}];
Coefficient[SolveValues[Det[M]==0,Subscript[e, n+1]][[1]],Evaluate[Array[Subscript[e, #]&,n]]]//FullSimplify
]


(* ::Subsection:: *)
(*parametricAtlas*)


(* ::Input::Initialization:: *)
boundaryAtlas[cnd_,vars_]:=Module[{cndList,allIxs,intList,bdryList,cndIxParamTuples,bdrySubsetIxs,lowerCndsSimple,lowerCnds},
cndList=cnd/.And->List;
(* only one region check: *)
If[Not[Head[cndList]===List],cndList={cndList}];
allIxs=Range[Length[cndList]];

intList=cndList/.LessEqual->Less;
bdryList=cndList/.LessEqual->Equal;
cndIxParamTuples=Table[
bdrySubsetIxs=Subsets[allIxs,{ii}];
lowerCndsSimple=Fold[And,bdryList[[#]]]&&Fold[And,intList[[Complement[allIxs,#]]]]&/@bdrySubsetIxs;
lowerCndsSimple=lowerCndsSimple/.Fold[And,{}]->True;
lowerCnds=BooleanConvert[Reduce[#,Evaluate[vars],Reals],"SOP"]&/@lowerCndsSimple;
(If[#2===False,Undefined,
With[{red=reduceParametricPieces[#2,vars]},
If[red==={},Undefined,{#3,#1,If[Head@#2===Or,List@@#2,{#2}],red}]
]
])&@@@Transpose@{lowerCndsSimple,lowerCnds,bdrySubsetIxs}/.Undefined->Sequence[]
,{ii,Range[1,Length[allIxs]]}];
(* will contain {} when a boundary intersection is not on the boundary of the intersecting set: *)
cndIxParamTuples=Flatten[cndIxParamTuples,1]
(* cndIxParamTuples = List of tuples {{regionIxs,simpleCnd,paramsLogical,paramsReduced},...}*)
]
atlasCol=AssociationThread[{"regionIxs","simpleCnd","paramsLogical","paramsReduced"}->Range[4]];

boundaryAtlasLookup[boundaryAtlas_,vars_,testPoint_]:=Module[{subsetIx,paramIx,paramVals},
subsetIx=LengthWhile[boundaryAtlas[[;;,atlasCol["simpleCnd"]]],!trep[#,vars,testPoint]&]+1;
Assert[subsetIx<=Length[boundaryAtlas]](* Not a boundary point *);
paramIx=LengthWhile[boundaryAtlas[[subsetIx,atlasCol["paramsLogical"]]],!trep[#,vars,testPoint]&]+1;
Assert[paramIx<=Length[boundaryAtlas]](* Could not find suitable param? Should not happen ... *);
paramVals=trep[boundaryAtlas[[subsetIx,atlasCol["paramsReduced"]]][[paramIx]][[2]],vars,testPoint];
{subsetIx,paramIx,paramVals}
]

boundaryAtlasPlot[atlas_,vars_]:=Module[{params=atlas[[;;,atlasCol["paramsReduced"]]],baseSurf,typeLens,typeLenRepElem,colors},
typeLens=Length/@params;
params=Flatten[params,1];
colors=cyclicTakeUpTo[getDiscreteColorTheme[DefaultColor],Length[params]];
typeLenRepElem=repelem[typeLens];
Show[Table[
baseSurf=params[[ii]];
Switch[Length[baseSurf[[2]]],
0,
Graphics3D[{(*colors[[typeLenRepElem[[ii]]]]*)Purple,Point[baseSurf[[1]]]}],
_,
plotParamPiece[baseSurf,vars,PlotStyle->colors[[typeLenRepElem[[ii]]]]]
]
,{ii,Length[params]}],PlotRange->All]
]

boundaryAtlasPolarParamsReduced[atlas_,vars_,ncList_]:=Module[{normalCones,generators},
Inner[Function[{setInclusionIx,edge},Table[
normalCones=ncList[[setInclusionIx]];
(* I want The convex hull of this: *)
generators=normalCones/.Thread[vars->param[[1]]]//Simplify;
Switch[Length[generators],
1,
{generators[[1]],param[[2]],param[[3]],{{0,1}}},
2,
{s generators[[1]]+(1-s)generators[[2]],Join[param[[2]],{s}],Join[param[[3]],{{0,1}}]},
_,
param(*Polygon[generators]*)(* Need to generalize above *)
]
,{param,edge}]],atlas[[;;,atlasCol["regionIxs"]]],atlas[[;;,atlasCol["paramsReduced"]]],List]
]


(* ::Input:: *)
(*cnd=({x,y,z} . {x,y,z}<=1/.x->x-1/2)&&({x,y,z} . {x,y,z}<=1/.x->x+1/2)&&({x,y,z} . {x,y,z}<=1/.z->z+1/2)&&({x,y,z} . {x,y,z}<=1/.z->z-1/2)*)
(*vars={x,y,z}*)
(*atlas=boundaryAtlas[cnd,vars];*)
(*testPoint=First[vars/.FindInstance[atlas[[5,atlasCol["simpleCnd"]]],vars]]*)
(*boundaryAtlasLookup[atlas,vars,testPoint]*)
(*boundaryAtlasPlot[atlas,vars]*)


(* ::Input:: *)
(*F=initializeSet[cnd,vars]*)
(*ncList=F["ncList"]*)


(* ::Input:: *)
(*ncList*)


(* ::Input:: *)
(*atlas//MatrixForm;*)
(*(* boundaryAtlasPolarParam *)*)
(*newParamsReduced=Inner[Function[{setInclusionIx,edge},Table[*)
(*normalCones=ncList[[setInclusionIx]];*)
(*(* I want The convex hull of this: *)*)
(*generators=normalCones/.Thread[F["vars"]->param[[1]]]//Simplify;*)
(*Switch[Length[generators],*)
(*1,*)
(*{generators[[1]],param[[2]],param[[3]],{{0,1}}},*)
(*2,*)
(*polarSurf={s generators[[1]]+(1-s)generators[[2]],Join[param[[2]],{s}],Join[param[[3]],{{0,1}}]};*)
(*polarSurf,*)
(*_,*)
(*param(*Polygon[generators]*)*)
(*]*)
(*,{param,edge}]],atlas[[;;,1]],atlas[[;;,4]],List];*)
(**)
(*(*Show[plotParamPiece[#,F["vars"]]&/@Flatten[newParamsReduced,1],PlotRange->All]*)*)
(*boundaryAtlasPlot[Transpose@ConstantArray[newParamsReduced,4],F["vars"]]*)


(* ::Input:: *)
(*newParamsReduced // MatrixForm*)


(* ::Input:: *)
(*params=Flatten[atlas[[;;,4]],1];*)
(*Show[Table[*)
(*baseSurf=params[[ii]];*)
(*normalCones=ncList[[Flatten@Position[setInclusionQ[[ii]],True]]];*)
(*(* I want The convex hull of this: *)*)
(*generators=normalCones/.Thread[f1["vars"]->baseSurf[[1]]]//Simplify;*)
(*Switch[Length[generators],*)
(*1,*)
(*polarSurf={generators[[1]],baseSurf[[2]],baseSurf[[3]],{{0,1}}};*)
(*plotParamPiece[polarSurf,f1["vars"],PlotStyle->colors[[typeLenRepElem[[ii]]]]],*)
(*2,*)
(*polarSurf={s generators[[1]]+(1-s)generators[[2]],Join[baseSurf[[2]],{s}],Join[baseSurf[[3]],{{0,1}}]};*)
(*Echo[polarSurf];*)
(*plotParamPiece[polarSurf,f1["vars"],PlotStyle->colors[[typeLenRepElem[[ii]]]]],*)
(*_,*)
(*Graphics3D[{colors[[typeLenRepElem[[ii]]]],Polygon[generators[[{1,3,2,4}]]]}]*)
(*]*)
(*,{ii,Length[params]}],PlotRange->All,ViewPoint->{1,2,1}]*)


(* ::Input:: *)
(*testPoint={0,0,1/2}*)
(*subsetIx=LengthWhile[cndIxParamTuples[[;;,2]],!trep[#,vars,testPoint]&]+1*)
(*Assert[subsetIx<=Length[cndIxParamTuples]](* Not a boundary point *)*)
(*paramIx=LengthWhile[cndIxParamTuples[[subsetIx,3]],!trep[#,vars,testPoint]&]+1*)
(*Assert[paramIx<=Length[cndIxParamTuples]](* Could not find suitable param? Should not happen ... *)*)
(*paramVals=trep[cndIxParamTuples[[subsetIx,4]][[paramIx]][[2]],vars,testPoint]*)


(* ::Input:: *)
(*reducedParamVerifier[redParam_,vars_,testPoint_]:=With[{cnd=Fold[And,#2[[1]]<=#1<=#2[[2]]&@@@Transpose[redParam[[{2,3}]]]]},*)
(*trep[cnd,vars,testPoint]*)
(*]*)


(* ::Input:: *)
(*typeLenRepElem=Flatten[ConstantArray[#,#2]&@@@Transpose@{Range[Length[typeLens]],typeLens}];*)
(*colors={Orange,Blue,Purple};*)
(**)
(*Show[Table[*)
(*baseSurf=params[[ii]];*)
(*normalCones=ncList[[Flatten@Position[setInclusionQ[[ii]],True]]];*)
(*(* I want The convex hull of this: *)*)
(*generators=normalCones/.Thread[f1["vars"]->baseSurf[[1]]]//Simplify;*)
(*Switch[Length[generators],*)
(*1,*)
(*polarSurf={generators[[1]],baseSurf[[2]],baseSurf[[3]],{{0,1}}};*)
(*plotParamPiece[polarSurf,f1["vars"],PlotStyle->colors[[typeLenRepElem[[ii]]]]],*)
(*2,*)
(*polarSurf={s generators[[1]]+(1-s)generators[[2]],Join[baseSurf[[2]],{s}],Join[baseSurf[[3]],{{0,1}}]};*)
(*Echo[polarSurf];*)
(*plotParamPiece[polarSurf,f1["vars"],PlotStyle->colors[[typeLenRepElem[[ii]]]]],*)
(*_,*)
(*Graphics3D[{colors[[typeLenRepElem[[ii]]]],Polygon[generators[[{1,3,2,4}]]]}]*)
(*]*)
(*,{ii,Length[params]}],PlotRange->All,ViewPoint->{1,2,1}]*)


(* ::Input:: *)
(*polarBoundaryAtlas[]*)


(* ::Input:: *)
(*f=initializeSet[x^2<=1,{x,y}]*)
(*f["nan"]*)
(*plot[f,5]*)


(* ::Input:: *)
(*Format[optIntSet[id_]]:=Module[{},id]*)
(*f=initializeSet[And[x^2<=1,y<=1],{x,y}]*)
(*f["nan"]*)
(*plot[f]*)


(* ::Input:: *)
(**)


(* ::Section:: *)
(*UI Development*)


(* ::Input:: *)
(*OpenerView[{Plus,x+y+z},True]*)


(* ::Subsection:: *)
(*v1*)


(* ::Input:: *)
(*optFun[ix_]["init","displayMode"]:="full"*)
(*Format[optFun[id_]]:=Module[{hlRules,f=optFun[id],d0={}(*KeyDrop[optFun[id]["data"],"parent"]*)(*optFun[id]["data"]*)},*)
(*Switch[f["displayMode"],*)
(*"full",*)
(*DynamicModule[{s=False},{OpenerView[{Plus,Dynamic@Refresh[If[s,optFun[id]["data"]],TrackedSymbols:>{s}]},Dynamic[s]],Checkbox[Dynamic[s]]}](*;*)
(*hlRules=#->Style[#,FontColor->Blue,FontWeight->Medium]&/@f["vars"];*)
(*Tooltip[Panel[Magnify[f["expr"]/.hlRules//TraditionalForm,1.25],FrameMargins->0,Background->Lighter[Gray,0.95]],d0]*),*)
(*"name",*)
(*Tooltip[Magnify[Style[f["name"],FontColor->Red,FontWeight->Medium]//TraditionalForm,1.25],d0]*)
(*]];*)
(*formatExpr[optFun[id_]]:=Module[{hlRules,f=optFun[id]},*)
(*hlRules=#->Style[#,FontColor->Blue,FontWeight->Medium]&/@f["vars"];*)
(*Tooltip[Panel[Magnify[f["expr"]/.hlRules//TraditionalForm,1.25],FrameMargins->0,Background->Lighter[Gray,0.95]],*)
(*{optFun,id,optFun[id]["name"]}]*)
(*]*)
(*formatName[optFun[id_]]:=Style[optFun[id]["name"],FontColor->Blue,FontWeight->Medium]*)
(*Format[optFun[id_]]:=DynamicModule[{x={},f=optFun[id]},*)
(*Dynamic[Refresh[DynamicModule[{usingNames=MemberQ[x,1],showingPanel=MemberQ[x,2],nameDisplay,selectorPanel},*)
(*nameDisplay=If[usingNames,formatName[f],formatExpr[f]];*)
(*selectorPanel=Panel[Row[{nameDisplay,TogglerBar[Dynamic[x],{1->If[usingNames,">","<"],2->If[showingPanel,"\[FilledUpTriangle]","\[FilledDownTriangle]"]}]},"  "],FrameMargins->0];*)
(*Column[{*)
(*Mouseover[If[showingPanel,selectorPanel,nameDisplay],selectorPanel],*)
(*Sequence@@If[!showingPanel,{},{Panel[*)
(*Dataset[f["data"]]*)
(*]}]*)
(*}]*)
(*],TrackedSymbols:>{x}]]*)
(*]*)
(*Clear[x]*)
(*Format[optMaxFun[id_]]:=Module[{f=optMaxFun[id],c=optMaxFun[id]["children"]},CirclePlus@@c]*)
(*f=initializeFunction[Max[x^2+ Sqrt[x y]+y^4,x],{x,y}]*)
(*f["nan"]*)


(* ::Subsection:: *)
(*v2*)


(* ::Input:: *)
(*Toggler[False,{True,False}]*)


(* ::Input:: *)
(*Button[Defer[Sort[\[SelectionPlaceholder]]],None,BaseStyle->"Evaluate"]*)


(* ::Input:: *)
(*Sort[\[SelectionPlaceholder]]*)


(* ::Input:: *)
(*optFun[ix_]["init","displayMode"]:="full"*)
(*Format[optFun[id_]]:=Module[{hlRules,f=optFun[id],d0={}(*KeyDrop[optFun[id]["data"],"parent"]*)(*optFun[id]["data"]*)},*)
(*Switch[f["displayMode"],*)
(*"full",*)
(*DynamicModule[{s=False},{OpenerView[{Plus,Dynamic@Refresh[If[s,optFun[id]["data"]],TrackedSymbols:>{s}]},Dynamic[s]],Checkbox[Dynamic[s]]}](*;*)
(*hlRules=#->Style[#,FontColor->Blue,FontWeight->Medium]&/@f["vars"];*)
(*Tooltip[Panel[Magnify[f["expr"]/.hlRules//TraditionalForm,1.25],FrameMargins->0,Background->Lighter[Gray,0.95]],d0]*),*)
(*"name",*)
(*Tooltip[Magnify[Style[f["name"],FontColor->Red,FontWeight->Medium]//TraditionalForm,1.25],d0]*)
(*]];*)
(*formatExpr[optFun[id_]]:=Module[{hlRules,f=optFun[id]},*)
(*hlRules=#->Style[#,FontColor->Blue,FontWeight->Medium]&/@f["vars"];*)
(*Panel[Magnify[f["expr"]/.hlRules//TraditionalForm,1.25],FrameMargins->0,Background->Lighter[Gray,0.95]]*)
(*]*)
(*formatExpr[optMaxFun[id_]]:=Module[{f=optMaxFun[id],c=optMaxFun[id]["children"]},*)
(*Panel[CirclePlus@@c]*)
(*]*)
(*formatName[(f_optFun|f_optMaxFun)]:=Style[f["name"],FontColor->Blue,FontWeight->Medium]*)
(*(*(h_optFun|h_optMaxFun|h_optSet|h_optIntSet)*)*)
(*dynamicOptFormater[type_[id_]]:=DynamicModule[{x={},f=type[id]},*)
(*Dynamic[Refresh[DynamicModule[{usingNames=MemberQ[x,1],showingPanel=MemberQ[x,2],nameDisplay,selectorPanel},*)
(*nameDisplay=If[usingNames,formatName[f],formatExpr[f]];*)
(*selectorPanel=Tooltip[Panel[Row[{Button[nameDisplay,If[showingPanel,x=DeleteCases[x,2],x=Append[x,2]],Appearance->"Frameless"],TogglerBar[Dynamic[x],{1->If[usingNames,">","<"],2->If[showingPanel,"\[FilledUpTriangle]","\[FilledDownTriangle]"]}]},"  "],FrameMargins->0],*)
(*{type,id,type[id]["name"]}];*)
(*Column[{*)
(*Mouseover[If[showingPanel,selectorPanel,nameDisplay],selectorPanel],*)
(*Sequence@@If[!showingPanel,{},{Panel[*)
(*Dataset[f["data"]]*)
(*]}]*)
(*}]*)
(*],TrackedSymbols:>{x}]]*)
(*]*)
(*Format[optFun[id_]]:=dynamicOptFormater[optFun[id]]*)
(*Format[optMaxFun[id_]]:=dynamicOptFormater[optMaxFun[id]]*)
(*(*Format[optFun[ix_]]:=myFormat[optFun[ix]]*)
(*Format[optMaxFun[ix_]]:=myFormat[optMaxFun[ix]]*)*)
(*(* There should just be a switch statement that overwrite formatters *)*)
(*Clear[x]*)
(*(*Format[optMaxFun[id_]]:=Module[{f=optMaxFun[id],c=optMaxFun[id]["children"]},CirclePlus@@c]*)*)
(*f=initializeFunction[Max[x^2+ Sqrt[x y]+y^4,x],{x,y}]*)
(*f["nan"]*)


(* ::Input:: *)
(*Mouseover[off,on]*)


(* ::Input:: *)
(*DynamicModule[{x=1},{Slider[Dynamic[x]],Dynamic[x=Max[0,x-0.01]]}]*)


(* ::Input:: *)
(**)


(* ::Input:: *)
(*Dynamic[Refresh[Magnify[TogglerBar[Dynamic[$CellContext`x$$], {1 -> If[MemberQ[$CellContext`x$$, 1], "<", ">"], 2 -> If[MemberQ[$CellContext`x$$, 2], "\[FilledUpTriangle]", "\[FilledDownTriangle]"]}, Appearance -> "Vertical"], 0.5], TrackedSymbols :> {$CellContext`x$$}], ImageSizeCache -> {13., {9.853613239200786, 12.146386760799214`}}]//FullForm*)


(* ::Input:: *)
(*DynamicModule[{s=False},{OpenerView[{Plus,Dynamic@Refresh[If[s,Assert[False];s],TrackedSymbols:>{s}]},Dynamic[s]],Checkbox[Dynamic[s]]}]*)


(* ::Input:: *)
(*FlipView[{40!,Plot[Sin[x],{x,0,2 Pi}],Factor[x^14-1]}]*)


(* ::Subsection:: *)
(*v3*)


(* ::Input:: *)
(*setOptFormat["dynamic"]*)
(*f=initializeFunction[Max[x^2+ Sqrt[x y]+y^4,x],{x,y}]*)
(*f["convexity"]*)
(*%[[1]]*)


(* ::Input:: *)
(*setOptFormat["expr"]*)


(* ::Input:: *)
(*setOptFormat["dynamic"]*)
(*f=initializeSet[2x^2<=1&&2y^2<=1,{x,y}]*)
(*f["gauge"]*)
(*f["data"]*)
(*objRelationGraph[f]*)


(* ::Input::Initialization:: *)
freeOptQ[expr_]:=And@@(FreeQ[expr,#]&/@{optFun,optMaxFun,optSet,optIntSet})
getPatterns[expr_,pat_]:=Last@Reap[expr/. a:pat:>Sow[a],_,Sequence@@#2&](* cases does not include head, even at level 0 *)
optCases[expr_]:=Flatten[getPatterns[expr,#]&/@{_optFun,_optMaxFun,_optSet,_optIntSet}]


(* ::Input:: *)
(*Cases[1,_Integer,0]*)


(* ::Input::Initialization:: *)
Options[objRelationGraph]={TrivialEdges->True};
objRelationGraph[f_,OptionsPattern[]]:=Block[{g},
visitedObjs={};
objQueue={f};
edgeList={};

While[Length[objQueue]>0,
Block[{ff=objQueue[[1]]},
relationalCandidates=Flatten[KeyValueMap[
With[{cases=optCases[#2]},If[Length[cases]>0,Function[{case},{ff,case,#1}]/@cases,Missing[]]]&,
ff["data"]
]/.Missing[]->Sequence[],1];
edgeList=Join[edgeList,DirectedEdge@@@relationalCandidates];
visitedObjs=Join[visitedObjs,{ff}];
objQueue=DeleteCases[objQueue,ff];
objQueue=Join[objQueue,Complement[relationalCandidates[[;;,2]],visitedObjs]];
]
];

g=Graph[edgeList,VertexLabels->"Name",EdgeLabels->"EdgeTag"];
If[Not@OptionValue[TrivialEdges],g=EdgeDelete[g,EdgeList[g][[Flatten@Position[SameQ[{},#]&/@StringCases[EdgeTags[g],___~~"Of"],False]]]]];
g
]


(* ::Input:: *)
(*f=initializeFunction[x^2+1,{x}]*)
(*f["epi"]["polar"]["polar"]["expr"]*)
(*objRelationGraph[f,TrivialEdges->False]*)


(* ::Input::Initialization:: *)
functionList[context_String:"Global`"]:=TableForm@Sort[HoldForm@@@Flatten[(ToExpression[#,InputForm,DownValues]&/@Names[context<>"*"])[[All,All,1]]]]


(* ::Input:: *)
(*visitedObjs={};*)
(*objQueue={f};*)
(*edgeList={};*)
(**)
(*While[Length[objQueue]>0,*)
(*Block[{f=objQueue[[1]]},*)
(*relationalCandidates=Flatten[KeyValueMap[*)
(*With[{cases=optCases[#2]},If[Length[cases]>0,Function[{case},{f,case,#1}]/@cases,Missing[]]]&,*)
(*ff["data"]*)
(*]/.Missing[]->Sequence[],1];*)
(*edgeList=Join[edgeList,DirectedEdge@@@relationalCandidates];*)
(*visitedObjs=Join[visitedObjs,{ff}];*)
(*objQueue=DeleteCases[objQueue,ff];*)
(*objQueue=Join[objQueue,Complement[relationalCandidates[[;;,2]],visitedObjs]];*)
(*]*)
(*];*)
(**)
(*Graph[edgeList,VertexLabels->"Name",EdgeLabels->"EdgeTag"]*)


(* ::Input:: *)
(*newObjQ=!MemberQ[#[[3]],visitedObjs]&/@relationalCandidates(* I don't know how much this matters *)*)


(* ::Input:: *)
(*Hold[1+1]*)


(* ::Input:: *)
(*First@First@Hold[False]*)


(* ::Section:: *)
(*Opt Classes*)


Clear[optObj, optFun, optSet, optISet, optPSet, optDSet]


(* ::Input::Initialization:: *)
DEBUG = False;


(* ::Subsection:: *)
(*optObj*)


(* ::Code::Initialization::Bold:: *)
(* basic stateful object that has inheritance *)
optObj[data_Association] := With[{ix = Unique[]},
    optObj[ix]["data"] = data;
    optObj[ix]
    ]
optObj[ix_]["get", prop_] := Lookup[optObj[ix]["data"], prop,
      With[{newProp = optObj[ix]["init", prop]},If[(*Not[First@newProp==="init"]*)True,AppendTo[optObj[ix]["data"], prop -> newProp]]]; 
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
    If[SameQ[Head@varsTMP, Symbol],
      varsTMP = {vars}
      ];
    If[SameQ[Head@exprTMP, List],
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


(* ::Subsection:: *)
(*optFun*)


(* ::Input::Initialization:: *)
DownValues[optFun]=ReplaceRepeated[DownValues[optObj],optObj->optFun];
SubValues[optFun]=ReplaceRepeated[SubValues[optObj],optObj->optFun];
sub[optFun[ix_],val_]:=optObj[ix]["expr"]/.Thread[optFun[ix]["vars"]->val]
optFun[ix_]["init","verbose"]:=DEBUG
optFun[ix_]["init","name"]:=Subscript[\[FormalF],ix]


(* ::Input::Initialization:: *)
optFun[ix_]["init","displayMode"]:="full"
(*Format[optFun[id_]]:=Module[{hlRules,f=optFun[id],d0={}(*KeyDrop[optFun[id]["data"],"parent"]*)},
Switch[f["displayMode"],
"full",
hlRules=#->Style[#,FontColor->Blue,FontWeight->Medium]&/@f["vars"];
Tooltip[Panel[Magnify[f["expr"]/.hlRules//TraditionalForm,1.25],FrameMargins->0,Background->Lighter[Gray,0.95]],d0],
"name",
Tooltip[Magnify[Style[f["name"],FontColor->Red,FontWeight->Medium]//TraditionalForm,1.25],d0]
]];*)


(* ::Input::Initialization:: *)
plotBoundsParser[vars_,bounds_:{}]:=Module[{b=bounds,nVars},nVars=Length[vars];
(*infer bounds*)
If[SameQ[b,{}],b=1];
(*default to unit box*)
If[NumberQ[b],b=b*{-1,1}];
If[Length[b]==2&&NumberQ[b[[1]]],b=Table[b,{nVars}]];
b=Join[List/@vars,b,2]]
plot[optFun[ix_],bounds_:{},varargin___]:=Module[{f=optFun[ix],b=plotBoundsParser[optFun[ix]["vars"],bounds]},
(*TODO: make manipulate if there are parameters*)
Switch[Length[f["vars"]],
1,Plot[f["expr"]//cvxReduce,Evaluate[Sequence@@b],varargin],
2,Plot3D[f["expr"]//cvxReduce,Evaluate[Sequence@@b],varargin],
_,Missing[]]
]
cplot[optFun[ix_],bounds_:{},varargin___]:=Module[{f=optFun[ix],b=plotBoundsParser[optFun[ix]["vars"],bounds]},
(*TODO: make manipulate if there are parameters*)
Switch[Length[f["vars"]],
1,Missing[],
2,ContourPlot[f["expr"]//cvxReduce,Evaluate[Sequence@@b],varargin],
3,ContourPlot3D[f["expr"]//cvxReduce,Evaluate[Sequence@@b],varargin],_,Missing[]]
]


(* ::Subsubsection:: *)
(*relation to optMaxFun*)


(* ::Input::Initialization:: *)
optFun[ix_]["init","parent"]:=Null


(* ::Subsubsection:: *)
(*related sets*)


(* ::Input::Initialization:: *)
optFun[ix_]["init","lev"]:=Module[{f=optFun[ix],d=optFun[ix]["data"],dObj},
dObj=initializeSet@@lev[d["expr"],d["vars"],1];

If[!SameQ[d["convexity"],Indeterminate],AppendTo[dObj["data"],"convex"->True]];
If[trep[d["expr"],d["vars"],ConstantArray[0,Length[d["vars"]]]]==0&&dObj["contains0"],AppendTo[dObj["data"],"gauge"->f]];(* 3.3.11 *)

dObj
]


(* ::Subsubsection:: *)
(*convexity properties*)


(* ::Input::Initialization:: *)
optFun[ix_]["init","convexity"]:=With[{d=optFun[ix]["data"]},FunctionConvexity[{d["expr"],d["cnd"]},d["vars"]]]
optFun[ix_]["init","convex"]:=optFun[ix]["data"]["convexity"]===1
optFun[ix_]["init","domain"]:=With[{d=optFun[ix]["data"]},initializeSet@@dom[d["expr"],d["vars"]]]
optFun[ix_]["init","epi"]:=With[{d=optFun[ix]["data"]},initializeSet@@epi[d["expr"],d["vars"]]]


(* ::Subsection:: *)
(*optMaxFun*)


(* ::Input::Initialization:: *)
DownValues[optMaxFun]=ReplaceRepeated[DownValues[optObj],optObj->optMaxFun];
SubValues[optMaxFun]=ReplaceRepeated[SubValues[optObj],optObj->optMaxFun];
sub[optMaxFun[ix_],val_]:=optMaxFun[ix]["expr"]/.Thread[optMaxFun[ix]["vars"]->val]
optMaxFun[ix_]["init","verbose"]:=DEBUG


(* ::Input::Initialization:: *)
optMaxFun[ix_]["init","children"]:=Module[{parts=optMaxFun[ix]["expr"]/.Max->List,children,myName},
children=If[Head[#]===optFun,#,optFun[#,optMaxFun[ix]["vars"]]]&/@parts;
AppendTo[optMaxFun[ix]["data"],"expr"->Max@@(#["expr"]&/@children)];(* inheritance is kind of tricky when *)
myName=optMaxFun[ix]["name"];
MapIndexed[AppendTo[#1["data"],"name"->Subscript[myName,#2[[1]]]/.Subscript[a_,Subscript[b_,c_]]:>Subscript[a,{b,c}]]&,children];
Map[AppendTo[#1["data"],"parent"->optMaxFun[ix]]&,children];
(*Map[AppendTo[#1["data"],"displayMode"->"name"]&,children];*)
children
]
optMaxFun[ix_]["init","name"]:=Subscript[\[FormalF],ix]


(* ::Input::Initialization:: *)
  (*Format[optMaxFun[id_]] := Module[{hlRules, d0 = KeyDrop[optMaxFun[id]["data"],"children"], c = optMaxFun[id]["data"]["children"]},
  Tooltip[Panel[c/.List->CirclePlus]//TraditionalForm,d0]]*)


(* ::Input::Initialization:: *)
optMaxFun[ix_]["init","epi"]:=Module[{c=optMaxFun[ix]["children"]},initializeSet[Fold[And,#["epi"]["expr"]&/@c],c[[1]]["epi"]["vars"],Name->epi[optMaxFun[ix]["name"]]]]


(* ::Input::Initialization:: *)
plot[optMaxFun[ix_],bounds_:{},varargin___]:=Module[{f=optMaxFun[ix],b=plotBoundsParser[optMaxFun[ix]["vars"],bounds]},
(*TODO: make manipulate if there are parameters*)
Switch[Length[f["vars"]],
1,Plot[f["expr"]//cvxReduce,Evaluate[Sequence@@b],varargin],
2,Plot3D[f["expr"]//cvxReduce,Evaluate[Sequence@@b],varargin],
_,Missing[]]
]
cplot[optMaxFun[ix_],bounds_:{},varargin___]:=Module[{f=optMaxFun[ix],b=plotBoundsParser[optMaxFun[ix]["vars"],bounds]},
(*TODO: make manipulate if there are parameters*)
Switch[Length[f["vars"]],
1,Missing[],
2,ContourPlot[f["expr"]//cvxReduce,Evaluate[Sequence@@b],varargin],
3,ContourPlot3D[f["expr"]//cvxReduce,Evaluate[Sequence@@b],varargin],_,Missing[]]
]


(* ::Subsection:: *)
(*optSet*)


(* ::Input::Initialization:: *)
DownValues[optSet]=ReplaceRepeated[DownValues[optObj],optObj->optSet];
SubValues[optSet]=ReplaceRepeated[SubValues[optObj],optObj->optSet];

sub[optSet[ix_],val_]:=optSet[ix]["expr"]/.Thread[optSet[ix]["vars"]->val]
optID[optSet[ix_]] := ix;
isComputed[optSet[ix_], key_] := KeyExistsQ[optSet[ix]["data"], key];
nVars[optSet[ix_]] := Length[optSet[ix]["vars"]]
optSet[ix_]["init","verbose"]:=DEBUG


(* ::Input::Initialization:: *)
(*Format[optSet[id_]]:=Module[{hlRules,f=optSet[id],d0={}(*KeyDrop[optSet[id]["data"],"parent"]*)},
Switch[f["displayMode"],
"full",
hlRules=#->Style[#,FontColor->Blue,FontWeight->Medium]&/@f["vars"];
Tooltip[Panel[Magnify[f["expr"]/.hlRules//TraditionalForm,1.25],FrameMargins->0],d0],
"name",
Tooltip[Magnify[Style[f["name"],FontColor->Purple,FontWeight->Medium]//TraditionalForm,1.25],d0]
]];*)


(* ::Input::Initialization:: *)
optSet[ix_]["init","name"]:=Subscript[C,ix]
optSet[ix_]["init","displayMode"]:="full"


(* ::Input::Initialization:: *)
plot[optSet[ix_],bounds_:{},varargin___]:=Module[{f=optSet[ix],b=plotBoundsParser[optSet[ix]["vars"],bounds]},
(*TODO: make manipulate if there are parameters*)
Switch[Length[f["vars"]],
2,RegionPlot[f["expr"]//cvxReduce,Evaluate[Sequence@@b],varargin],
3,RegionPlot3D[f["expr"]//cvxReduce,Evaluate[Sequence@@b],varargin],
_,Missing[]]
]


(* ::Subsubsection:: *)
(*relation to optIntSet*)


(* ::Input::Initialization:: *)
optISet[ix_]["init","parent"]:=Null


(* ::Subsubsection:: *)
(*convexity properties*)


(* ::Input::Initialization:: *)
optSet[ix_]["init","name"]:=Subscript[C,ix]
optSet[ix_]["init","displayMode"]:="full"
optSet[ix_]["init","contains0"]:=With[{f=optSet[ix]},Reduce[Implies[f["cnd"],Reduce[sub[f,Table[0,Length[f["vars"]]]]]],f["vars"],Reals]]
optSet[ix_]["init","bounded"]:=With[{f=optSet[ix]},Reduce[Implies[f["cnd"],bounded[cvxReduce[f["expr"]],f["vars"]]],f["vars"],Reals]]


(* ::Input:: *)
(**)


(* ::Subsection:: *)
(*optIntSet*)


(* ::Input::Initialization:: *)
DownValues[optIntSet]=ReplaceRepeated[DownValues[optObj],optObj->optIntSet];
SubValues[optIntSet]=ReplaceRepeated[SubValues[optObj],optObj->optIntSet];
sub[optIntSet[ix_],val_]:=optIntSet[ix]["expr"]/. Thread[optIntSet[ix]["vars"]->val]
optIntSet[ix_]["init","verbose"]:=DEBUG


(* ::Input::Initialization:: *)
(*Format[optIntSet[id_]]:=Module[{hlRules,d0=optIntSet[id]["data"],c=optIntSet[id]["data"]["children"]},Tooltip[Panel[c/. List->And]//TraditionalForm,d0]]*)


(* ::Input::Initialization:: *)
optIntSet[ix_]["init","children"]:=Module[{parts=optIntSet[ix]["expr"]/.And->List,children,myName},
Assert[AllTrue[parts,Head[#]===LessEqual&]];
children=optSet[#[[1]]-#[[2]]+1<=1,optIntSet[ix]["vars"]]&/@parts;
myName=optIntSet[ix]["name"];
MapIndexed[AppendTo[#1["data"],"name"->Subscript[myName,#2[[1]]]/.Subscript[a_,Subscript[b_,c_]]:>Subscript[a,{b,c}]]&,children];
Map[AppendTo[#1["data"],"parent"->optIntSet[ix]]&,children];
(*Map[AppendTo[#1["data"],"displayMode"->"name"]&,children];*)
children
]
optIntSet[ix_]["init","name"]:=Subscript[C,ix]


(* ::Input::Initialization:: *)
plot[optIntSet[ix_],bounds_:{},varargin___]:=Module[{f=optIntSet[ix],b=plotBoundsParser[optIntSet[ix]["vars"],bounds]},
(*TODO: make manipulate if there are parameters*)
Switch[Length[f["vars"]],
2,RegionPlot[f["expr"]//cvxReduce,Evaluate[Sequence@@b],varargin],
3,RegionPlot3D[f["expr"]//cvxReduce,Evaluate[Sequence@@b],varargin],
_,Missing[]]
]
boundaryPlot[optIntSet[ix_],varargin___]:=Module[{f=optIntSet[ix]},
(*TODO: make manipulate if there are parameters*)
boundaryAtlasPlot[f["boundaryAtlas"],f["vars"]]
]


(* ::Subsubsection:: *)
(*Properties From Children*)


(* ::Input::Initialization:: *)
optIntSet[ix_]["init","contains0"]:=Module[{c=optIntSet[ix]["children"]},Reduce[And@@Map[#["contains0"]&,c]]]
optIntSet[ix_]["init","bounded"]:=Module[{c=optIntSet[ix]["children"]},
If[Reduce[And@@Map[#["bounded"]&,c]]===True,True,
With[{f=optIntSet[ix]},bounded[f["expr"],f["vars"]]]
]]
optIntSet[ix_]["init","gauge"]:=Module[{c=optIntSet[ix]["children"],d=optIntSet[ix]["data"]},
initializeFunction[Max[Map[#["gauge"]&,c]],d["vars"]]
]
optIntSet[ix_]["init","ncList"]:=Module[{c=optIntSet[ix]["children"],d=optIntSet[ix]["data"]},
Map[#["normalizedNormalCone"]&,c]
]


(* ::Subsubsection:: *)
(*Manual Properties*)


(* ::Input::Initialization:: *)
optIntSet[ix_]["init","boundaryAtlas"]:=Module[{obj=optIntSet[ix]},boundaryAtlas[obj["expr"],obj["vars"]]]


(* ::Subsubsection:: *)
(*Functions*)


(* ::Input::Initialization:: *)
project[optIntSet[ix_],x_]:=x/sub[optIntSet[ix]["gauge"],x]


(* ::Subsection:: *)
(*Fancy Input Forms*)


(* ::Input::Initialization:: *)
BoundaryConditions[f_optSet]:=f["expr"]
NormalizedNormalCone[f_optSet]:=Function[Evaluate[f["vars"]],f["NormalizedNormalCone"]]
Subscript[\!\(\*OverscriptBox[\(\[ScriptCapitalN]\), \(^\)]\), f_optSet]:=NormalizedNormalCone[f]
Polar[f_optSet]:=f["polar"]
f_optSet^\[Degree]:=Polar[f]
Gauge[f_optSet]:=Function[Evaluate[f["vars"]],f["gauge"]]
Subscript[\[Gamma], f_optSet]:=Gauge[f]


(* ::Section:: *)
(*Opt Classes Tests*)


(* ::Input::Initialization:: *)
Options[initializeFunction]={Conditions->True,Name->Automatic}
initializeFunction[{f_,cnds_},vars_,OptionsPattern[]]:=initializeFunction[f,vars,
Sequence@@(
If[#1===Conditions,
#1->cnds&&Element[Alternatives@@vars,Reals]&&OptionValue[#1],
#1->OptionValue[#1]
]&@@@Options[initializeFunction]
)]
initializeFunction[f_,vars_,OptionsPattern[]]:=Module[{f0},
f0=optFun[{f,OptionValue[Conditions]},vars];
If[Not[OptionValue[Name]===Automatic],AppendTo[f0["data"], "name"->OptionValue[Name]]];
f0
]
initializeFunction[f_Max,vars_,OptionsPattern[]]:=Module[{F0},
F0=optMaxFun[{f,OptionValue[Conditions]},vars];
If[Not[OptionValue[Name]===Automatic],AppendTo[F0["data"], "name"->OptionValue[Name]]];
F0["children"];
F0
]



(* ::Subsection:: *)
(*intersection*)


(* ::Input:: *)
(*initializeSet[{x,y} . {x,y}<=1,{x,y}]*)


(* ::Input::Initialization:: *)
Options[initializeSet]={Conditions->True,Name->Automatic}
initializeSet[{f_,cnds_},vars_,OptionsPattern[]]:=initializeSet[f,vars,
Sequence@@(
If[#1===Conditions,
#1->cnds&&Element[Alternatives@@vars,Reals]&&OptionValue[#1],
#1->OptionValue[#1]
]&@@@Options[initializeSet]
)]

initializeSet[f_GreaterEqual,vars_,OptionsPattern[]]:=initializeSet[-f[[2]]<=f[[1]],vars,Sequence@@(#1->OptionValue[#1]&@@@Options[initializeSet])]
initializeSet[f_LessEqual,vars_,OptionsPattern[]]:=Module[{f0},
f0=optSet[{f,OptionValue[Conditions]},vars];
If[Not[OptionValue[Name]===Automatic],AppendTo[f0["data"], "name"->OptionValue[Name]]];
f0
]
initializeSet[f_And,vars_,OptionsPattern[]]:=Module[{F0},
F0=optIntSet[{f,OptionValue[Conditions]},vars];
If[Not[OptionValue[Name]===Automatic],AppendTo[F0["data"], "name"->OptionValue[Name]]];
F0["children"];
F0
]



(* ::Input:: *)
(*f1=optSet[{x,y} . {x,y}<=1,{x,y}]*)
(*f1["name"]*)


(* ::Input:: *)
(*f1=initializeSet[{x,y} . {x,y}<=1,{x,y},Name->F]*)
(*f1["name"]*)


(* ::Input:: *)
(**)


(* ::Input:: *)
(*Reduce[Implies[True,x]]*)


(* ::Input::Initialization:: *)
optSet[ix_]["init","support"]:=Module[{f=optSet[ix],d=optSet[ix]["data"],sol,dObj,polarReccCnds},
Echo[{FreeQ[d["expr"],indicator],f["bounded"]},{f["name"],"Support"}];

If[FreeQ[d["expr"],indicator]||f["bounded"]===True,

If[!f["bounded"],

(*If[isComputed[f,"gauge"],Echo[f["gauge"]]];*)

If[f["contains0"]&&isComputed[f,"gauge"],
(* Basu, A. 3.3.11 *)
polarReccCnds=polar[Reduce[f["gauge"]["expr"]==0//cvxReduce,f["gauge"]["vars"],Reals],f["gauge"]["vars"]];
If[f["verbose"],Echo[StringForm["polarReccCnds `` computed using gauge",polarReccCnds],{f["name"],"Support"}]];
,
polarReccCnds=polarRecc[d["expr"]//cvxReduce,d["vars"]];
If[f["verbose"],Echo[StringForm["polarReccCnds `` computed directly",polarReccCnds],{f["name"],"Support"}]];
];,
polarReccCnds={True,{}}
];

sol=simpleSupport[d["expr"]/.indicator[_]->0,d["vars"],polarReccCnds[[1]]&&d["cnd"]];

(*Echo[{polarReccCnds}];*)
sol=Assuming[polarReccCnds[[1]]&&d["cnd"],Simplify[sol]]+indicator[polarReccCnds[[1]]]

If[!FreeQ[sol,formalVector[d["vars"]][[1]]],
If[f["verbose"],Echo[StringForm["Support computation of `` using stationarySupport failed: ``",{d["expr"]/.indicator[_]->0,d["vars"]},sol],{f["name"],"Support"}]];
(* TODO: better control flow *)
sol=support[d["expr"]//cvxReduce,d["vars"]];
If[f["verbose"],Echo[StringForm["Support `` computed directly",sol],{f["name"],"Support"}]];
,
If[f["verbose"],Echo[StringForm["Support `` computed using stationarySupport",sol],{f["name"],"Support"}]];
];

,
sol=support[d["expr"]//cvxReduce,d["vars"]];
If[f["verbose"],Echo[StringForm["Support `` computed directly",sol],{f["name"],"Support"}]];
];

Echo[List[sol,Fold[And,Element[#,Reals]&/@d["vars"]]&&d["cnd"]]];
dObj=initializeFunction[{cvxResolveOverReals[sol,d["vars"],d["cnd"]],d["cnd"]},d["vars"],Name->\[Sigma][f["name"]]];
Echo[dObj["expr"],{f["name"],"Support"}];
If[True,AppendTo[dObj["data"],"supportOf"->f]];

dObj
]
optSet[ix_]["init","polar"]:=Module[{f=optSet[ix],d=optSet[ix]["data"],dObj,polarGauge,polarExpr},
polarGauge=f["support"];
polarExpr=FullSimplify[cvxResolveOverReals[polarGauge["expr"]<=1,d["vars"],d["cnd"]],d["cnd"]];

dObj=initializeSet[{polarExpr,d["cnd"]},f["vars"](*formalCovector[f["vars"]]*),Name->polar[f["name"]]];
If[!f["contains0"],
(*Echo[contains0polar];*)
polarGauge=initializeFunction[Max[polarGauge,0],f["vars"],Name->gauge[polar[f["name"]]]]
];

If[True,AppendTo[dObj["data"],"polarOf"->f]];

If[True,AppendTo[dObj["data"],"contains0"->True]];(* always true *)

If[True,AppendTo[polarGauge["data"],"lev"->dObj]];
If[True,AppendTo[dObj["data"],"gauge"->polarGauge]];
(*If[f["contains0"],AppendTo[dObj["data"],"bounded"->True]];*)(* this has to be stated for optSet[x^2-y-1<=1/.Thread[{x,y}->RotationMatrix[0].({x,y}-1/8)],{x,y}]["polar"], removed for epi graphs *)
If[isComputed[f,"polarOf"],AppendTo[dObj["data"],"zeroHull"->f["polarOf"]]];

If[f["contains0"],AppendTo[dObj["data"],"polar"->f]
];

dObj
]
optSet[ix_]["init","gauge"]:=Module[{f=optSet[ix],d=optSet[ix]["data"],dObj,polarGauge},
dObj=optSet[ix]["polar"]["support"];
If[True,AppendTo[dObj["data"],"lev"->f]];
dObj
]
optSet[ix_]["init","normalizedNormalCone"]:=Grad[optSet[ix]["gauge"]["expr"],optSet[ix]["vars"]]


(* ::Input:: *)
(*FunctionConvexity[Sqrt[a^2 x^2+b^2 y^2],{x,y},Reals]*)


(* ::Input:: *)
(*f=initializeSet[{{x/a,y/b} . {x/a,y/b}<=1,(a|b)\[Element]Reals&&(a|b)!=0},{x,y}]*)
(*f["polar"]["polar"]*)
(*g=objRelationGraph[f,TrivialEdges->False]*)


(* ::Input:: *)
(*MatchQ[1/2,1/_Integer]*)


(* ::Input:: *)
(*Simplify[x^2+y^2>=0,(x|y)\[Element]Reals]*)


(* ::Input:: *)
(*vars={x,y}*)
(*Power[x^2+y^2,1/2]<=1*)


(* ::Input:: *)
(*Reduce[x^2+y^2>=0,Reals]*)


(* ::Input:: *)
(*cnd=({x,y,z} . {x,y,z}<=1/.x->x-1/2)&&({x,y,z} . {x,y,z}<=1/.x->x+1/2)&&({x,y,z} . {x,y,z}<=1/.z->z+1/2)&&({x,y,z} . {x,y,z}<=1/.z->z-1/2)*)
(*vars={x,y,z}*)
(*F0=initializeSet[cnd,vars,Name->F]*)
(*F0["contains0"]*)


(* ::Input:: *)
(*.*)


(* ::Input:: *)
(*Module[{hlRules, f =F0},*)
(*  hlRules = # -> Style[#, FontColor -> Blue, FontWeight -> Medium] & /@ f["vars"];*)
(*  Tooltip[*)
(*   Panel[Magnify[f["expr"] /. hlRules // TraditionalForm, 1.25], *)
(*    FrameMargins -> 0],*)
(*   f["data"]]]*)


(* ::Input:: *)
(*F0["expr"]*)


(* ::Input::Initialization:: *)
formatMode="dynamic";
setOptFormat[formatMode_]:=Switch[formatMode,
"bare",(FormatValues[#]={})&/@{optFun,optMaxFun,optSet,optIntSet};,
"expr",
(*optInstance[_,_,ix_,h_]:=h[ix];*)
exprFormater[(f_optFun|f_optMaxFun|f_optSet|f_optIntSet)]:=optInstance[f["expr"],f["vars"],f[[1]],Head@f];
Format[optFun[id_]]:=exprFormater[optFun[id]];
Format[optMaxFun[id_]]:=exprFormater[optMaxFun[id]];
Format[optSet[id_]]:=exprFormater[optSet[id]];
Format[optIntSet[id_]]:=exprFormater[optIntSet[id]];,
"noButton",
formatExpr[optFun[id_]]:=Module[{hlRules,f=optFun[id]},
hlRules=#->Style[#,FontColor->Blue,FontWeight->Medium]&/@f["vars"];
Panel[Magnify[f["expr"]/.hlRules//TraditionalForm,1.25],FrameMargins->0,Background->Lighter[Gray,0.95]]
];
formatExpr[optSet[id_]]:=Module[{hlRules,f=optSet[id]},
hlRules=#->Style[#,FontColor->Blue,FontWeight->Medium]&/@f["vars"];
Panel[Magnify[f["expr"]/.hlRules//TraditionalForm,1.25],FrameMargins->0]
];
formatExpr[optMaxFun[id_]]:=Module[{f=optMaxFun[id],c=optMaxFun[id]["children"]},
Panel[CirclePlus@@Deploy/@c,FrameMargins->0]
];
formatExpr[optIntSet[id_]]:=Module[{f=optIntSet[id],c=optIntSet[id]["children"]},
Panel[And@@Deploy/@c,FrameMargins->0]
];
formatName[(f_optFun|f_optMaxFun)]:=Style[f["name"],FontColor->Blue,FontWeight->Medium];
formatName[(f_optSet|f_optIntSet)]:=Style[f["name"],FontColor->Purple,FontWeight->Medium];
(*(h_optFun|h_optMaxFun|h_optSet|h_optIntSet)*)
dynamicOptFormater[(f_optFun|f_optMaxFun|f_optSet|f_optIntSet)]:=Tooltip[formatExpr[f],{Head[f],f[[1]],f["name"]}];
Format[optFun[id_]]:=dynamicOptFormater[optFun[id]];
Format[optMaxFun[id_]]:=dynamicOptFormater[optMaxFun[id]];
Format[optSet[id_]]:=dynamicOptFormater[optSet[id]];
Format[optIntSet[id_]]:=dynamicOptFormater[optIntSet[id]];,
"dynamic",
formatExpr[optFun[id_]]:=Module[{hlRules,f=optFun[id]},
hlRules=#->Style[#,FontColor->Blue,FontWeight->Medium]&/@f["vars"];
Panel[Magnify[f["expr"]/.hlRules//TraditionalForm,1.25],FrameMargins->0,Background->Lighter[Gray,0.95]]
];
formatExpr[optSet[id_]]:=Module[{hlRules,f=optSet[id]},
hlRules=#->Style[#,FontColor->Blue,FontWeight->Medium]&/@f["vars"];
Panel[Magnify[f["expr"]/.hlRules//TraditionalForm,1.25],FrameMargins->0]
];
formatExpr[optMaxFun[id_]]:=Module[{f=optMaxFun[id],c=optMaxFun[id]["children"]},
Panel[CirclePlus@@Deploy/@c,FrameMargins->0]
];
formatExpr[optIntSet[id_]]:=Module[{f=optIntSet[id],c=optIntSet[id]["children"]},
Panel[And@@Deploy/@c,FrameMargins->0]
];
formatName[(f_optFun|f_optMaxFun)]:=Style[f["name"],FontColor->Blue,FontWeight->Medium];
formatName[(f_optSet|f_optIntSet)]:=Style[f["name"],FontColor->Purple,FontWeight->Medium];
(*(h_optFun|h_optMaxFun|h_optSet|h_optIntSet)*)
dynamicOptFormater[(f_optFun|f_optMaxFun|f_optSet|f_optIntSet)]:=DynamicModule[{showingPanel=False,usingNames=False,tabChoice=1},
Dynamic[Refresh[DynamicModule[{nameDisplay,selectorPanel},
nameDisplay=If[usingNames,formatName[f],formatExpr[f]];
selectorPanel=Tooltip[Toggler[Dynamic[showingPanel],#->nameDisplay&/@{True,False}],
{Head[f],f[[1]],f["name"]}];
Column[{
selectorPanel,
Sequence@@If[!showingPanel,{},{TabView[{
"DataSet"->Dataset[f["data"]],
"Plots"->Dynamic[Refresh[
If[tabChoice==2,
(* [Preset dropdown] [code textbox] [copy button] [evaluate button]*)
plot[f],
"Generating ..."]
,TrackedSymbols:>{tabChoice}]]
},Dynamic[tabChoice],FrameMargins->0]}]
}]
],TrackedSymbols:>{showingPanel}]]
];
Format[optFun[id_]]:=dynamicOptFormater[optFun[id]];
Format[optMaxFun[id_]]:=dynamicOptFormater[optMaxFun[id]];
Format[optSet[id_]]:=dynamicOptFormater[optSet[id]];
Format[optIntSet[id_]]:=dynamicOptFormater[optIntSet[id]];
]
setOptFormat["noButton"]


(* ::Subsection:: *)
(*unbounded*)


(* ::Input:: *)
(*setOptFormat["noButton"]*)
(*f=initializeFunction[Max[(x-1)^2,(x+1)^2],{x}]*)
(*f["epi"]["gauge"]*)
(*g=objRelationGraph[f,TrivialEdges->False]*)


(* ::Input:: *)
(*FullSimplify[Max[1/Sqrt[a/(x^2+y^2)],-(Sqrt[x^2+y^2]/Sqrt[a])],x\[Element]Reals&&y\[Element]Reals&&a>0]*)


(* ::Input:: *)
(*f["polar"]["data"]*)


(* ::Input:: *)
(*plot[f["polar"],3]*)


(* ::Input:: *)
(*Reduce[Alternatives[-x-Sqrt[2] Sqrt[x] Sqrt[y]-y,-x+Sqrt[2] Sqrt[x] Sqrt[y]-y]\[Element]Reals&&(x|y)\[Element]Reals,{x,y}]*)
(*RegionPlot[%,{x,-1,1},{y,-1,1}]*)


(* ::Input:: *)
(*Plot3D[List[-x-Sqrt[2] Sqrt[x] Sqrt[y]-y,-x+Sqrt[2] Sqrt[x] Sqrt[y]-y],{x,-3,3},{y,-3,3}]*)


(* ::Input:: *)
(*ContourPlot[-x+Sqrt[2] Sqrt[x] Sqrt[y]-y,{x,-3,3},{y,-3,3}]*)


(* ::Input:: *)
(**)


(* ::Input:: *)
(*cplot[f["polar"]["polar"]["gauge"],4]*)
(*plot[f["polar"]["polar"]](* we should actually be slicing a multi avlued function*)*)


(* ::Input:: *)
(*plot[f["polar"],5]*)


(* ::Input:: *)
(**)


(* ::Input:: *)
(*FunctionConvexity[-x-y+Sqrt[x^2+y^2],{x,y}]*)


(* ::Input:: *)
(*f["expr"]*)
(*f["support"]["expr"]*)
(*f["polar"]["expr"]*)


(* ::Subsection:: *)
(*Support Functions (Implicit)*)


(* ::Input::Initialization:: *)
On[Assert];


(* ::Input::Initialization:: *)
trep[expr_,vars_,inp_]:=expr/.Thread[vars->inp]
mtrep[expr_,vars_,inp_]:=expr/.Thread[vars->#]&/@inp


(* ::Input::Initialization:: *)
(* useres should avoid custom specifcation of \[FormalX], \[FormalS], and \[FormalZeta] do to use in codebase (as well as \[FormalL], due to use as generic symbol)*)
formalScalar=\[FormalX];

formalVector[n_Integer]:=Array[Subscript[formalScalar,#]&,n]
formalVector[n_Integer,m_]:=Array[Superscript[Subscript[formalScalar,#],m]&,n]
formalVector[n_List,varargin___]:=With[{x=formalVector[Length[n],varargin]},If[SameQ[n,x],x/.formalScalar->\[FormalY],x]]

formalVectors[n_,m_]:=formalVector[n,#]&/@Range[m]

formalParameter[varargin___]:=formalVector[varargin]/.formalScalar->\[FormalS]
formalCovector[varargin___]:=formalVector[varargin]/.formalScalar->\[FormalZeta]


(* ::Input:: *)
(*Solve[formalVector[3,1]==3formalVector[3,2],Evaluate[formalVector[3,2]]]*)


(* ::Input::Initialization:: *)
repelem[ix_List]:=Flatten[ConstantArray[#1,#2]&@@@Transpose@{Range[Length[ix]],ix}]
repelem[v_List,ix_List]:=v[[repelem[ix]]]


(* ::Input:: *)
(*repelem[{a,b,c},{3,4,8}]*)


(* ::Input::Initialization:: *)
cyclicTakeUpTo[v_List,n_Integer]:=v[[Mod[Range[n]-1,Length[v]]+1]]


(* ::Input::Initialization:: *)
(* https://mathematica.stackexchange.com/questions/54486/how-to-access-new-colour-schemes-in-version-10 *)
showDiscreteColorThemes[]:=Grid[{#,getDiscreteColorTheme[#]}&/@("Color"/. Charting`$PlotThemes),Dividers->All]
getDiscreteColorTheme[name_]:=Cases["DefaultPlotStyle"/.(Method/.Charting`ResolvePlotTheme[name,ListPlot]),_RGBColor,Infinity]


(* ::Input::Initialization:: *)
pwGetPairs[f_Piecewise]:=Module[{vals,cnds},
vals=Append[f[[1,;;,1]],f[[2]]];
cnds=f[[1,;;,2]];
cnds=Append[cnds,Not@Fold[Or,cnds]];
{vals,cnds}]
pwAddConditionIgnoreLast[f_Piecewise,cnd_]:=Module[{},
f[[1,;;,2]]=#&&cnd&/@f[[1,;;,2]];f
]
pwAddCondition[f_Piecewise,cnd_]:=Module[{vals,cnds},
{vals,cnds}=pwGetPairs[f];
cnds=(#&&cnd&)/@cnds;
Piecewise[{vals,cnds}\[Transpose],Undefined[]]
]


(* ::Input::Initialization:: *)
(*TODO: pwDropLastSafe *)
pwDropLast[f_Piecewise]:=f/.Piecewise->\[FormalL]//.\[FormalL][a_List,b_]:>Piecewise[a[[1;;-2]],a[[-1,1]]]


(* ::Input::Initialization:: *)
forceString[x_]:=If[Head@x===String,x,ToString[x]]


(* ::Input::Initialization:: *)
Clear[cvxReduce]
cvxReduceCrawler[f_[a___]]:=f@@(cvxReduce/@{a})
cvxReduceCrawler[a_Symbol]:=a
cvxReduceCrawler[a_?NumberQ]:=a
cvxReduceCrawler[indicator[cnd_]]:=Piecewise[{{0,cnd}},Infinity]
cvxReduce[x_]:=cvxReduceCrawler[x]//PiecewiseExpand


(* ::Input:: *)
(*Piecewise[{{a,b>0},{b,a>0}},0]+indicator[b>0]//cvxReduce*)


(* ::Input:: *)
(*cvxReduce[x^2+y^2<=a]*)


(* ::Input::Initialization:: *)
cvxResolveOverReals[f_[a___],s___]:=f@@(cvxResolveOverReals[#,s]&/@{a})
cvxResolveOverReals[a_Symbol,___]:=a
cvxResolveOverReals[a_?NumberQ,___]:=a

(* level set of 1 anyway, common case mathematica misses *)
cvxResolveOverReals[Power[expr_,1/2]<=1,vars_,cnd_]:=If[
Simplify[expr>=0,cnd]===True||FullSimplify[Reduce[expr>=0&&Im[Alternatives@@vars]==0,Complexes],cnd]===True,
cvxResolveOverReals[expr,vars,cnd]<=1,Power[cvxResolveOverReals[expr,vars,cnd],1/2]<=1
]

cvxResolveOverReals[a_+indicator[b_],vars_,cnd_]:=cvxResolveOverReals[a,vars,cnd&&b]+indicator[b]


cvxResolveOverReals[Max[a_,b_],vars_,cnd_]:=Which[
FullSimplify[Reduce[a>=b&&Im[Alternatives@@vars]==0,Complexes],cnd]===True,a,
FullSimplify[Reduce[a<=b&&Im[Alternatives@@vars]==0,Complexes],cnd]===True,b,
True,Max@@(cvxResolveOverReals[#,vars,cnd]&/@{a,b})
]
cvxResolveOverReals[Min[a_,b_],vars_,cnd_]:=Which[
FullSimplify[Reduce[a<=b&&Im[Alternatives@@vars]==0,Complexes],cnd]===True,a,
FullSimplify[Reduce[a>=b&&Im[Alternatives@@vars]==0,Complexes],cnd]===True,b,
True,Max@@(cvxResolveOverReals[#,vars,cnd]&/@{a,b})
]
(* This old way breaks: f=initializeSet[{ x, y}.{ x,y}<=1/.Thread[{x,y}->{x,y}+1],{x,y}]
f["polar"]["polar"]*)


(* ::Input:: *)
(*cvxResolveOverReals[Max[-x-Sqrt[2] Sqrt[x] Sqrt[y]-y,-x+Sqrt[2] Sqrt[x] Sqrt[y]-y],{x,y},x<=0&&y<=0]//RepeatedTiming*)


(* ::Subsection:: *)
(*Indicator Functions*)


(* ::Input::Initialization:: *)
MakeBoxes[closedIntervalBracket[x__],fmt:TraditionalForm]^:=RowBox[{"[",RowBox[Riffle[BoxForm`ListMakeBoxes[{x},fmt],","]],"]"}]

Format[ind[fx_,x_,{a_,b_}],TraditionalForm]:=Subscript[\[Delta], x \[Element] closedIntervalBracket[a,b]][fx]
Format[ind[x_,x_,{a_,b_}],TraditionalForm]:=Subscript[\[Delta], closedIntervalBracket[a,b]][x]
Format[indicator[x_],TraditionalForm]:=Subscript[\[Delta], closedIntervalBracket[x]]


(* ::Input:: *)
(**)


(* ::Input::Initialization:: *)
MakeBoxes[closedIntervalBracket[x__],fmt:TraditionalForm]^:=RowBox[{"[",RowBox[Riffle[BoxForm`ListMakeBoxes[{x},fmt],","]],"]"}]

Format[ind[fx_,x_,{a_,b_}],TraditionalForm]:=Subscript[\[Delta], x \[Element] closedIntervalBracket[a,b]][fx]
Format[ind[x_,x_,{a_,b_}],TraditionalForm]:=Subscript[\[Delta], closedIntervalBracket[a,b]][x]


(* ::Input:: *)
(*fun[b+a_.]:=a*)


(* ::Input:: *)
(*fun[b+1]*)


(* ::Input:: *)
(*fun[b]*)


(* ::Input::Initialization:: *)
ind[\[Lambda]_. fz_+\[Delta]_.,z_Symbol,{a_,b_}]/;
!And[\[Lambda]===1,\[Delta]===0]&&!FreeQ[fz,z]:=
ind[fz,z,{( a-\[Delta])/\[Lambda],( b-\[Delta])/\[Lambda]}]


(* ::Input:: *)
(*ind[7x^2+b,x,{-1,1}]*)
(*%//TraditionalForm*)


(* ::Input::Initialization:: *)
SetAttributes[ind,HoldFirst](* this is only so g can be Sqrt *)
ind[g_[fz_],z_Symbol,{a_,b_}]/;
!FreeQ[fz,z]&&
(If[FunctionInjective[g[fz],z,PerformanceGoal->"Speed"]===True,True,
FunctionInjective[{g[fz],a<z<b},z,PerformanceGoal->"Speed"]]):=
Module[{gi=InverseFunction[g[#]&],bnds,fm},
(* TODO: Faster methods in other (not purely symbolic) cases *)
fm=FunctionMonotonicity[g[z],z,PerformanceGoal->"Speed"];
If[SameQ[Head@fm,ConditionalExpression],
fm=fm[[1]]];(* TODO: Context tracking *)
Switch[fm,
1,ind[fz,z,{gi[a],gi[b]}],
0,{Indeterminate,"ind with constant mapping"},
-1,ind[fz,z,{gi[b],gi[a]}],
Indeterminate,bnds={gi[b],gi[a]};ind[fz,z,{Min@@bnds,Max@@bnds}]
]
]


(* ::Input:: *)
(*SetAttributes[ind2,HoldFirst]*)
(*ind2[g_[fz_],z_Symbol,{a_,b_}]:=If[FunctionInjective[g[fz],z,PerformanceGoal->"Speed"]===True,True,*)
(*FunctionInjective[{g[fz],a<z<b},z,PerformanceGoal->"Speed"]]*)


(* ::Input:: *)
(*ind[4Log[4z+5]+8,z,{-1,1}]*)
(*ind[4Log[4z+5]+8,z,m{-1,1}+b]*)
(*ind[z^2,z,{3,8}]*)


(* ::Input:: *)
(*FunctionInjective[{z^2,3<z<8},z,PerformanceGoal->"Speed"]*)


(* ::Input:: *)
(**)


(* ::Subsection:: *)
(*Algebra Tools*)


(* ::Input:: *)
(*isLinearIn[expr_,var_Symbol]:=*)


(* ::Subsection:: *)
(*Implicit Region Tests*)


(* ::Input::Initialization:: *)
zeroSymmetric[cons_LessEqual,vars_]:=Reduce[ForAll[vars,
Implies[cons,trep[cons,vars,-vars]]],
vars,Reals]
bounded[cons_,vars_]:=Resolve[Exists[\[FormalL],ForAll[Evaluate[vars],cons,vars . vars<=\[FormalL]]]]


(* ::Input:: *)
(*zeroSymmetric[{x,y} . {x,y}<=3,{x,y}]*)


(* ::Input:: *)
(*bounded[{x,y} . {x,y}<=3,{x,y}]*)


(* ::Input:: *)
(**)


(* ::Subsection:: *)
(*Implicit Region > Implicit Region Transforms*)


(* ::Input::Initialization:: *)
polar[expr_,vars_]:=Module[{newVars=formalCovector[vars],pCnd},
pCnd=ForAll[Evaluate[newVars],trep[expr,vars,newVars],vars . newVars<=1];
{Reduce[pCnd,newVars,Reals],vars}]


(* ::Input::Initialization:: *)
recc[expr_,vars_]:=Module[{newVars=formalCovector[vars],reccCnd},
reccCnd=ForAll[Evaluate[newVars],trep[expr,vars,newVars],trep[expr,vars,newVars+vars]];
{Reduce[reccCnd,newVars,Reals],vars}]
polarRecc[expr_,vars_]:=polar@@recc[expr,vars]


(* ::Subsection:: *)
(*Implicit Region > Function Transforms*)


(* ::Input::Initialization:: *)
support[expr_,vars_]:=With[{newVars=formalVector[vars]},
Maximize[{vars . newVars,trep[expr,vars,newVars]},newVars,Reals][[1]]
]


(* ::Subsection:: *)
(*Function Tests*)


(* ::Input::Initialization:: *)
convex[expr_,vars_]:=Module[{x=formalVectors[vars,2],c={\[FormalL],1-\[FormalL]}},
(* this is amlos never used in favor of FunctionComplexity *)
Reduce[ForAll[Evaluate[Append[vars,\[FormalL]]],0<\[FormalL]<1,
trep[expr,vars,c . x]<=c . mtrep[expr,vars,x]],
vars,Reals]
]
positiveHomogeneous[expr_,vars_]:=Reduce[ForAll[Evaluate[Append[vars,\[FormalL]]],\[FormalL]>0,
\[FormalL] expr==trep[expr,vars,\[FormalL] vars]],
vars,Reals]
(* sublinear - Great example: when working with classes, dfn 3.3.1 or prop 3.3.2 can be used *)
sublinear[expr_,vars_]:=Module[{x=formalVectors[vars,2],l=formalParameter[2]},
Reduce[ForAll[Evaluate[Flatten[Join[x,l]]],Fold[And,#>0&/@l],
trep[expr,vars,l . x]==l . mtrep[expr,vars,x]],
vars,Reals]
]


(* ::Input:: *)
(*positiveHomogeneous[ #,{x,y}]&/@{x^2+y^2,Sqrt[a x^2+y^2]}*)


(* ::Input:: *)
(*convex[ #,{x,y}]&/@{x^2+y^2,Sqrt[a x^2+y^2]}(* the second one taks forever, wold be good to speed test with c1 / c2 convex*)*)


(* ::Input:: *)
(*Clear[x]*)


(* ::Input:: *)
(*sublinear[ #,{x,y}]&/@{x^2+y^2,Sqrt[a x^2+y^2]}*)


(* ::Subsection:: *)
(*Function Transforms*)


(* ::Input::Initialization:: *)
epi[expr_,vars_]:=With[{x=formalVector[Length[vars]+1]},{trep[expr,vars,x[[;;-2]]]<=x[[-1]],x}]
(*lev[expr_,vars_,alpha_:1]:={expr<=alpha,vars}
dom[expr_,vars_]:={expr<Infinity,vars}*)


(* ::Input:: *)
(*epi[x^2+y^2,{x,y},cvxReduce]*)


(* ::Input::Initialization:: *)
Clear[dom,lev]
dom[Plus[expr_,indicator[cnd_]],vars_]:=dom[{expr,cnd},vars]
dom[{Plus[expr_,indicator[cnd_]],cnd0_},vars_]:=dom[{expr,cnd&&cnd0},vars]

dom[expr_,vars_]:=dom[{expr,True},vars]
dom[{expr_,cnd_},vars_]:={Reduce[expr<Infinity&&cnd,vars,Reals],vars}

lev[expr_,vars_,alpha_:1]:=lev[{expr/.indicator[_]->0,dom[expr,vars][[1]]},vars,alpha]
lev[{expr_,cnd_},vars_,alpha_:1]:={expr<=alpha&&cnd&&dom[expr,vars][[1]],vars}


(* ::Input:: *)
(*lev[{x,y} . {x,y}+indicator[x<1],{x,y}]*)


(* ::Input::Initialization:: *)
(*cvxReduce[{expr_,True}]:=expr
cvxReduce[expr_:Except[_List]]:=cvxReduce[{expr,True}]
cvxReduce[expr_Plus]:=cvxReduce[{expr,True}]
cvxReduce[{expr_,cnd_}]:=Piecewise[{{cvxReduce[expr],cnd}},Indeterminate]
cvxReduce[{Plus[expr_,indicator[cndi_]],cnd_}]:=Piecewise[{{cvxReduce[expr],cndi&&cnd//Reduce},{Infinity,!cndi&&cnd//Reduce}},Indeterminate]
cvxReduce[Plus[expr_,indicator[cndi_]]]:=Piecewise[{{cvxReduce[expr],cndi}},Infinity]
cvxReduce[LessEqual[a_,b_]]:=LessEqual[cvxReduce[a],cvxReduce[b]]*)


(* ::Input:: *)
(*cvxReduce[{a x+indicator[x<1],a>0}]*)
(*cvxReduce[a x+indicator[x<1]+indicator[x>-9]]//PiecewiseExpand*)


(* ::Input:: *)
(*cvxReduce[a x+7indicator[x<1]+indicator[x>-9]]*)


(* ::Input:: *)
(*dom[x+indicator[x<1]+indicator[x>-8],{x,y}]*)


(* ::Input:: *)
(**)


(* ::Input:: *)
(*lev[Plus[expr_,indicator[cnd_]],vars_,alpha_:1]:={expr<=alpha,vars}*)


(* ::Input::Initialization:: *)
subgradient[expr_,vars_]:=Module[{x=vars,y=formalVector[vars],z=formalCovector[vars]},
Reduce[ForAll[y,
(y-x) . z<=trep[expr,vars,y]-trep[expr,vars,x]],
z,Reals]
]


(* ::Input:: *)
(*subgradient[Abs[x],{x}]*)
(*subgradient[Max[x/2,x^2],{x}]*)


(* ::Input:: *)
(*reduceParametricPieces[BooleanConvert[subgradient[Max[x/2,x^2],{x}],"DNF"],{x}]//MatrixForm*)


(* ::Input:: *)
(*Reduce[(x<0&&Subscript[\[FormalZeta], 1]==-1)||(x==0&&-1<=Subscript[\[FormalZeta], 1]<=1)||(x>0&&Subscript[\[FormalZeta], 1]==1),{x}]*)


(* ::Input::Initialization:: *)
subgradientPiecewiseMultiValued[expr_,vars_]:=With[{pVars=formalCovector[vars],sg=subgradient[expr,vars]},mapPiecewiseValues[Switch[#,
_Integer,#,(* catches Piecewise default zero case *)
_Equal,With[{f=Flatten[pVars/.{ToRules[#]}]},If[Length[f]==1,f[[1]],ImplicitRegion[#,Evaluate[pVars]]]],
_,ImplicitRegion[#,Evaluate[pVars]]
]&,nestedPiecewiseFromHierarchicalLogic[sg,pVars]]]


(* ::Input:: *)
(*subgradientPiecewiseMultiValued[Max[x/2,x^2],{x}]*)


(* ::Input::Initialization:: *)
c1SubgradientR1[f_,{var_}]:=Module[{deriv,disc,points},
(* does not check jump discontinuities! *)
(* Convex 1-var *)
deriv=D[f,var];
(*Find the points of discontinuity*)
disc=FunctionDiscontinuities[deriv,var];
(*Find the actual points where discontinuity occurs*)
points=SolveValues[disc,var];
(*Glue the derivative together at points of discontinuity*)
PiecewiseExpand@Piecewise[
(*For each point of discontinuity,form an interval*)
Append[{
Interval[{
Limit[deriv,var->#,Direction->"FromAbove"],Limit[deriv,var->#,Direction->"FromBelow"]
}],
var==#
}&/@points,
(*For other points,simply use the derivative*)
{deriv,True}]
]
]


(* ::Input:: *)
(*f=Piecewise[{{x,0<x<1},{2*x-1,x>=1},{-x,x<=0}},0];*)
(*Plot[f,{x,-1,2}]*)
(*RepeatedTiming[c1SubgradientR1[f,{x}],1]*)
(*RepeatedTiming[sg=subgradientPiecewiseMultiValued[f,{x}],1]*)


(* ::Input::Initialization:: *)
ClearAll[solvePiecewise]
toRegion[f_]:=Module[{f0=f,ir},
(* Reduces pwmv function with 'Interval' and dervied ImplicitRegions to one with just ImplicitRegions. *)
(* Do reduction of ImplicitRegion *)
f0=f0/.ImplicitRegion->ir;
f0=f0//.{
Interval[{a_,b_}]:>ir[a<=y<=b,{y}],
ir[fxy_,{y_}]+fx_:> ir[fxy/.y->y-fx,{y}]
};
f0=f0/.ir->ImplicitRegion;
(* Return reduced function *)
f0
];
solvePiecewise[eq_,var_]:=Module[
{lhs,rhs,rel,pieces,regionPieces,nonRegionPieces,regionSolutions,nonRegionSolutions,solutions},
(*TODO: Fix lhs needing to be equation *)
(*Get left hand side and right hand side of the equation*)
If[Head[eq]===Equal,
{lhs,rhs}=List@@eq;
rel=Equal,
lhs=eq[[1]];
rhs=eq[[2]];
rel=Head[eq]];
lhs=toRegion[lhs];
(*Get piecewise pieces*)
pieces=Transpose@pwGetPairs[lhs];
(*Separate region pieces and non-region pieces*)
regionPieces=Select[pieces,Head[#[[1]]]===ImplicitRegion&];
nonRegionPieces=Select[pieces,Head[#[[1]]]=!=ImplicitRegion&];
(*Process each region piece*)
regionSolutions=(r|->Element[rhs,r[[1]]]&&r[[2]])/@regionPieces;
(*Echo[regionPieces//MatrixForm];*)
(*Echo[{regionPieces,Reduce[Or@@regionSolutions,var,Reals],ImplicitRegion[Reduce[Or@@regionSolutions,var,Reals],var]}];*)
(*Process each non-region piece*)
nonRegionSolutions=(expr|->rel[expr[[1]],rhs]&&expr[[2]])/@nonRegionPieces;
(*Echo[Reduce[Or@@nonRegionSolutions,var,Reals]];*)
(*Join all solutions*)
solutions=Join[regionSolutions,nonRegionSolutions];
(*Create final implicit region*)
ImplicitRegion[Reduce[Or@@solutions,var,Reals],var]]


(* ::Input:: *)
(*sg=c1SubgradientR1[Piecewise[{{x,0<x<1},{2*x-1,x>=1},{-x,x<=0}},0],{x}]*)
(*solvePiecewise[sg<={0},{x}]*)


(* ::Input:: *)
(*Plot3D[Abs[x]+Abs[y],{x,-1,1},{y,-1,1}]*)


(* ::Input:: *)
(*nestedPiecewiseFromHierarchicalLogic[sg0,formalCovector[2]]*)


(* ::Input:: *)
(*sg0=subgradient[Abs[x]+Abs[y],{x,y}]*)


(* ::Input:: *)
(*sg=subgradientPiecewiseMultiValued[Abs[x]+Abs[y],{x,y}]*)


(* ::Input:: *)
(*solvePiecewise[sg=={0,0},{x,y}]*)
(**)
(*RegionPlot[3 y<=x<y||(y==0&&x==0),{x,-1,1},{y,-1,1}]*)


(* ::Input:: *)
(*!((x < 0 && x - y > 0) || (x < 0 && x - y == 0) || (x < 0 && x - y < *)
(*    0 && y < 0) || (x < 0 && y == 0) || x < 0 || (x == 0 && y == 0) || (x*)
(*     == 0 && y < 0) || x == 0 || y < 0 || y == 0 || (y > 0 && x - y > 0) *)
(*    || x - y == 0) // Reduce*)


(* ::Input:: *)
(*sg=subgradientPiecewiseMultiValued[Abs[x]+Abs[y],{x,y}]//pwDropLast//PiecewiseExpand*)
(*solvePiecewise[sg=={0,0},{x,y}]*)
(*RegionPlot[3 y<=x<y||(y==0&&x==0),{x,-1,1},{y,-1,1}]*)
(*(* I blame PiecewiseExpand*)*)


(* ::Subsection:: *)
(*parametricPiece*)


(* ::Input::Initialization:: *)
toInequality[p_]:=p/.{
Less[a_,b_,c_]:>Inequality[a,Less,b,Less,c],
LessEqual[a_,b_,c_]:>Inequality[a,LessEqual,b,LessEqual,c],
(* assuming the variable of interest is always on the left (based on reduce) *)
Less[a_,b_]:>Inequality[-Infinity,Less,a,Less,b],
LessEqual[a_,b_]:>Inequality[-Infinity,Less,a,LessEqual,b],
Greater[a_,b_]:>Inequality[b,LessEqual,a,Less,Infinity],
GreaterEqual[a_,b_]:>Inequality[b,Less,a,Less,Infinity]};
toInequalityLeftBiasedToCenter=toInequality;


(* ::Input:: *)
(*vars = {x, y, z}*)
(**)
(*bounds = {{-x y, x y}, {0, 1}, {y, y}}*)


(* ::Input::Initialization:: *)
(* for ordering generation for-loops, like in ParametricPlot *)
varUsageOrdering[exprs_,vars_]:=OrderingBy[Transpose[{vars,exprs}],!FreeQ[#[[2]],#[[1]]]&]


(* ::Input:: *)
(*{vars,exprs}={{y,x},{{-(1/2) Sqrt[3+4 x-4 x^2],-(1/2) Sqrt[3+4 x-8 x^2]},{1/16 (5-Sqrt[119]),1/24 (5-Sqrt[166])}}}*)
(*OrderingBy[Transpose[{vars,exprs}],!FreeQ[#[[2]],#[[1]]]&]*)
(*{vars,exprs}={{x,y},{{0,1/24 (-3+5 Sqrt[6])},{-(1/2) Sqrt[3-4 x-4 x^2],-(1/2) Sqrt[3-4 x-8 x^2]}}}*)
(*OrderingBy[Transpose[{vars,exprs}],!FreeQ[#[[2]],#[[1]]]&]*)


(* ::Input:: *)
(*exprs*)


(* ::Input:: *)
(*FreeQ[{-(1/2) Sqrt[3-4 x-4 x^2],-(1/2) Sqrt[3-4 x-8 x^2]},x]*)


(* ::Input:: *)
(*exprs*)


(* ::Input:: *)
(*Outer[!FreeQ[#2,#1]&,vars,exprs]*)
(*AdjacencyGraph[Boole[%]]*)
(*DepthFirstScan[%]*)


(* ::Input::Initialization:: *)
sortedSubsetIndices[subset_,superset_]:=With[
(* things not in superset go at end *)
{orderInBigList=Flatten[Position[superset,#]&/@subset/.{}->Infinity]},
Ordering[orderInBigList,All,LessEqual]
]


(* ::Input::Initialization:: *)
reduceParametricPiece[p_,vars_:{}]:=Module[{(*pSplit,pHeads,eqIxs,mixedInEqIxs,constIxs,pOut*)},
(* reduce each parametric peice into a list: {{f[x],g[y],h[z]}, {x,y}, {{x0,x1},{y0,y1}}}, that is, {[Parametric Equations], [Parametric Variables], [Parametric Bounds]}*)
pSplit=p/.And->List//toInequality;
pHeads=Head/@pSplit;
eqIxs=Flatten@Position[pHeads,Equal];
mixedInEqIxs=Flatten@Position[pHeads,Inequality];
Assert[Length[Join[eqIxs,mixedInEqIxs]]==Length[p]];
If[Length[mixedInEqIxs]==0,
pOut={First[vars//.{ToRules[p]}],{},{}},
pOut={If[eqIxs==={},vars,First[vars//.{ToRules[Fold[And,pSplit[[eqIxs]]]]}]],pSplit[[mixedInEqIxs]][[;;,3]],Transpose@{pSplit[[mixedInEqIxs]][[;;,1]],pSplit[[mixedInEqIxs]][[;;,5]]}};
];
constIxs=Flatten@Position[MemberQ[pOut[[2]],#]&/@vars,False,1];
pOut[[1]]=pOut[[1]]/.Thread[vars[[constIxs]]->pOut[[1]][[constIxs]]];
(*pOut[[3]]=pOut[[3]]/.Thread[vars[[constIxs]]->pOut[[1]][[constIxs]]];*)
pOut
]
reduceParametricPieces[p_,vars_]:=If[Head[p]===Or,reduceParametricPiece[#,vars]&/@List@@p,{reduceParametricPiece[p,vars]}]


(* ::Input::Initialization:: *)
plotParamPiece[p_,vars_,varagin___]:=Module[{constIxs,ordering},If[Length[p[[1]]]==2,
If[p[[2]]==={},
Graphics[Point[p[[1]]]],
constIxs=Flatten@Position[MemberQ[p[[2]],#]&/@vars,False,1];
ordering=varUsageOrdering[p[[3]],p[[2]]];
ParametricPlot[p[[1]]/.Thread[vars[[constIxs]]->p[[1]][[constIxs]]],Evaluate[Sequence@@((Transpose@Join[{p[[2]][[ordering]]},Transpose@p[[3]][[ordering]]])/.{{x_,-Infinity,b_}:>{x,(b-1),b},{x_,b_,Infinity}:>{x,b,(b+1)}})],varagin]
],
If[p[[2]]==={},
Graphics3D[Point[p[[1]]]],
constIxs=Flatten@Position[MemberQ[p[[2]],#]&/@vars,False,1];
ordering=varUsageOrdering[p[[3]],p[[2]]];
ParametricPlot3D[p[[1]]/.Thread[vars[[constIxs]]->p[[1]][[constIxs]]],Evaluate[Sequence@@((Transpose@Join[{p[[2]][[ordering]]},Transpose@(p[[3]][[ordering]]//N//Re)])/.{{x_,-Infinity,b_}:>{x,(b-1),b},{x_,b_,Infinity}:>{x,b,(b+1)}})],varagin]
]
]]


(* ::Input:: *)
(*cnd=({x,y,z} . {x,y,z}<=1/.x->x-1/2)&&({x,y,z} . {x,y,z}<=1/.x->x+1/2)&&({x,y,z} . {x,y,z}<=1/.z->z+1/2)&&({x,y,z} . {x,y,z}<=1/.z->z-1/2)(*&&x+y+z<=1/4*)*)
(*vars={x,y,z}*)
(*atlas=boundaryAtlas[cnd,vars];*)
(*testPoint=First[vars/.FindInstance[atlas[[5,atlasCol["simpleCnd"]]],vars]]*)
(*boundaryAtlasLookup[atlas,vars,testPoint]*)
(*boundaryAtlasPlot[atlas,vars]*)
(**)


(* ::Input::Initialization:: *)
piecewiseNestedQ[expr_]:=Length[Position[expr,Piecewise]]>1
piecewiseValueWrapper[expr_Piecewise]:=Piecewise[{piecewiseValueWrapper[#1],#2}&@@@#1,piecewiseValueWrapper[#2]]&@@expr
mapPiecewiseValues[fun_,expr_]:=piecewiseValueWrapper[expr]/.piecewiseValueWrapper->fun


(* ::Input:: *)
(*pVars=formalCovector[1];*)
(*pw=nestedPiecewiseFromHierarchicalLogic[sg,pVars]*)
(*mapPiecewiseValues[Switch[#,*)
(*_Integer,#,(* catches Piecewise default zero case *)*)
(*_Equal,With[{f=Flatten[pVars/.{ToRules[#]}]},If[Length[f]==1,f[[1]],f]],*)
(*_,ImplicitRegion[#,Evaluate[pVars]]*)
(*]&,pw]*)
(*%/.x->1/2*)


(* ::Input:: *)
(*sg=subgradient[Abs[x]+Abs[y],{x,y}];*)
(*pw=nestedPiecewiseFromHierarchicalLogic[sg,formalCovector[2]];*)


(* ::Input:: *)
(*headMapLowest[fun_,expr_]:=Module[{lowestPositions=MaximalBy[Position[pw,Piecewise],Length]},]*)


(* ::Input:: *)
(*MaximalBy[Position[pw,Piecewise],Length]*)


(* ::Input::Initialization:: *)
nestedPiecewiseFromHierarchicalLogic[expr_,pVars_]:=Block[{exprPairedCndVal},
(* Assumes expr is "Tree-Like" with pVars at the lowest level. Example: 
nestedPiecewiseFromHierarchicalLogic[
(x>=0 && ((y>=0 && (z==x)) || (y<0 && (z==y)))) || (x<0 && (x<z<y)),
z] *)
(* pVars are parametric vars, these are the the variables that are NOT part of the Piecewise conditions *)
exprPairedCndVal=expr//.And[cnd_?(FreeQ[#,Alternatives@@pVars]&),val_]:>{val,cnd};
(* there is some porperty of the operator Or that makes it have to be spoofed (or else it stays persistent as Head) *)
exprPairedCndVal/.Or->\[FormalL]//.\[FormalL][x___List]:>Piecewise[{x}]/.\[FormalL]->Or
]


(* ::Input:: *)
(*sg=subgradient[Max[x/2,x^2],{x}]*)
(*nestedPiecewiseFromHierarchicalLogic[sg,formalCovector[2]]*)


(* ::Input:: *)
(*sg=subgradient[Abs[x]+Abs[y],{x,y}];*)
(*nestedPiecewiseFromHierarchicalLogic[sg,formalCovector[2]]*)


(* ::Subsection:: *)
(*HalfSpaces*)


(* ::Input::Initialization:: *)
int[R_]:=RegionDifference[R,RegionBoundary[R]]
originRegion[n_]:=ImplicitRegion[x==Table[0,n],x]


(* ::Input::Initialization:: *)
orthCompAff[AffineSpace[points_List]]:=Module[
(* The complement returned here will intersect the AffineSpace at the first point provided in it's definition. Not sure of rigor here...

Issues: This definition is "numeric" over the points due to the usage of Select and Orthogonalize.*)
{R=AffineSpace[points],p0=points[[1]],pCen,pCenOrth},
pCen=Table[p-p0,{p,points}];
pCenOrth=Select[Orthogonalize[pCen~Join~IdentityMatrix[RegionEmbeddingDimension[R]]],Norm[#]>0&][[Length[points];;]];
AffineSpace[{p0}~Join~Table[p+p0,{p,pCenOrth}]]
]
orthCompAff[AffineSpace[points_List],center_]:=TransformedRegion[
orthCompAff[AffineSpace[points]],
TranslationTransform[-points[[1]]+center]]


(* ::Input:: *)
(*R=AffineSpace[{{0,1,0},{0,0,0},{0,0,1}}];*)
(*Show[Graphics3D[{Orange,R,Blue,orthCompAff[R],Point[R[[1,1]]]}]]*)


(* ::Input::Initialization:: *)
ray[origin_,direction_]:=ConicHullRegion[{origin},{direction}]


(* ::Input:: *)
(*Graphics@ConicHullRegion[{{0,0}},{{1,1}}]*)


(* ::Subsection:: *)
(*lagrangeStationaryPoints*)


(* ::Input::Initialization:: *)
(* find solutions to Subscript[inf, cons] expr if exper is convex *)
lagrangeStationaryPoints[expr_,cons_Equal,vars_List]:=expr/. Solve[Eliminate[D[expr-\[Lambda] (cons[[2]]-cons[[1]]),{Join[vars,{\[Lambda]}]}]==0,\[Lambda]],vars]


(* ::Subsection:: *)
(*polarGenerators[pts_] (Discrete)*)


(* ::Input:: *)
(*<<"https://gist.githubusercontent.com/jasondbiggs/c3d9410af3195da514a442be5b563ab8/raw/80ac5074077f0d4b1366540c8c710e35cb530ddd/NDConvexHull.m"*)
(*(* https://mathematica.stackexchange.com/questions/113492/how-to-generate-higher-dimensional-convex-hull *)*)
(*CHNQuickHull[{{0,0,1},{1,2,1},{1,1,1},{6,9,1}}]*)


(* ::Subsection:: *)
(*Conic Hull (Implicit)*)


(* ::Input::Initialization:: *)
toLevelRegion[ImplicitRegion[expr_LessEqual,vars_]]:=levelRegion[expr[[1]]-expr[[2]]+1,vars]
(* implicit regions don't get wrapped until later, when we are going class mode *)

conicHull2[expr_,vars_]:=Module[{dim=Length[vars],g=Grad[expr[[1]],vars]},
(* slightly fancy version *)
(* assumes convexity *)
If[dim==2,
ConicHullRegion[{{0,0}},SolveValues[vars . g==0&&(expr/.LessEqual->Equal),vars]],
ImplicitRegion[Reduce[vars . g==0&&expr,vars,Reals],vars]
]
]

conicHull[expr_,vars_]:=Module[{dim=Length[vars],g=Grad[expr[[1]],vars]},
(* assumes convexity *)
{Reduce[vars . g==0&&expr,vars,Reals],vars}
]


(* ::Input:: *)
(*expr=(x-1)^2-y+2<=1*)
(*vars={x,y};*)
(*conicHull[expr,vars]*)


(* ::Input:: *)
(*dim=Length[vars]*)
(*g=Grad[expr[[1]],vars]*)
(*(* assumes convexity *)*)
(*If[dim==2,*)
(*ConicHullRegion[{{0,0}},SolveValues[Reduce[vars . g==0&&(expr/.LessEqual->Equal),vars,Reals],vars]],*)
(*ImplicitRegion[Reduce[vars . g==0&&expr,vars,Reals],vars]*)
(*]*)
(*g/.Thread[{x,y}->Transpose[{{-(Sqrt[3]/2),3/2},{Sqrt[3]/2,3/2}}]]*)
(*Graphics[{conicHull[expr,vars],ConicHullRegion[{{0,0}},Transpose@{{-Sqrt[3],Sqrt[3]},{-1,-1}}]}]*)


(* ::Input:: *)
(*expr=({x,y} . {x,y}<=1/.y->y-2)*)
(*vars={x,y};*)
(*RegionConvert[conicHull[expr,vars],"Implicit"]*)


(* ::Subsection:: *)
(*Active region (Intersection with parametric conic hull)*)


(* ::Input:: *)
(*impl={x,y,z} . {x,y,z}<=1/.x->x-3*)
(*f=impl[[1]]-impl[[2]]*)
(*0<={x,y,z} . Grad[f,{x,y,z}]&&(impl/.LessEqual->Equal)*)
(*BooleanConvert[Reduce[%,{x,y,z},Reals],"DNF"]*)


(* ::Subsection:: *)
(*polarParameterization*)


(* ::Input::Initialization:: *)
polarParameterization[param_,vars_]:=Module[{n=Length[param],grad=Transpose[Grad[param,vars]],
e,M},
M=Transpose[{
Array[Subscript[e, #]&,n+1],
param~Join~{1},
Sequence@@Join[
Array[grad[[##]]&,{n-1,n}],
ConstantArray[{0},n-1]
,2]
}];
Coefficient[SolveValues[Det[M]==0,Subscript[e, n+1]][[1]],Evaluate[Array[Subscript[e, #]&,n]]]//FullSimplify
]


(* ::Subsection:: *)
(*parametricAtlas*)


(* ::Input::Initialization:: *)
boundaryAtlas[cnd_,vars_]:=Module[{cndList,allIxs,intList,bdryList,cndIxParamTuples,bdrySubsetIxs,lowerCndsSimple,lowerCnds},
cndList=cnd/.And->List;
(* only one region check: *)
If[Not[Head[cndList]===List],cndList={cndList}];
allIxs=Range[Length[cndList]];

intList=cndList/.LessEqual->Less;
bdryList=cndList/.LessEqual->Equal;
cndIxParamTuples=Table[
bdrySubsetIxs=Subsets[allIxs,{ii}];
lowerCndsSimple=Fold[And,bdryList[[#]]]&&Fold[And,intList[[Complement[allIxs,#]]]]&/@bdrySubsetIxs;
lowerCndsSimple=lowerCndsSimple/.Fold[And,{}]->True;
lowerCnds=BooleanConvert[Reduce[#,Evaluate[vars],Reals],"SOP"]&/@lowerCndsSimple;
(If[#2===False,Undefined,
With[{red=reduceParametricPieces[#2,vars]},
If[red==={},Undefined,{#3,#1,If[Head@#2===Or,List@@#2,{#2}],red}]
]
])&@@@Transpose@{lowerCndsSimple,lowerCnds,bdrySubsetIxs}/.Undefined->Sequence[]
,{ii,Range[1,Length[allIxs]]}];
(* will contain {} when a boundary intersection is not on the boundary of the intersecting set: *)
cndIxParamTuples=Flatten[cndIxParamTuples,1]
(* cndIxParamTuples = List of tuples {{regionIxs,simpleCnd,paramsLogical,paramsReduced},...}*)
]
atlasCol=AssociationThread[{"regionIxs","simpleCnd","paramsLogical","paramsReduced"}->Range[4]];

boundaryAtlasLookup[boundaryAtlas_,vars_,testPoint_]:=Module[{subsetIx,paramIx,paramVals},
subsetIx=LengthWhile[boundaryAtlas[[;;,atlasCol["simpleCnd"]]],!trep[#,vars,testPoint]&]+1;
Assert[subsetIx<=Length[boundaryAtlas]](* Not a boundary point *);
paramIx=LengthWhile[boundaryAtlas[[subsetIx,atlasCol["paramsLogical"]]],!trep[#,vars,testPoint]&]+1;
Assert[paramIx<=Length[boundaryAtlas]](* Could not find suitable param? Should not happen ... *);
paramVals=trep[boundaryAtlas[[subsetIx,atlasCol["paramsReduced"]]][[paramIx]][[2]],vars,testPoint];
{subsetIx,paramIx,paramVals}
]

boundaryAtlasPlot[atlas_,vars_]:=Module[{params=atlas[[;;,atlasCol["paramsReduced"]]],baseSurf,typeLens,typeLenRepElem,colors},
typeLens=Length/@params;
params=Flatten[params,1];
colors=cyclicTakeUpTo[getDiscreteColorTheme[DefaultColor],Length[params]];
typeLenRepElem=repelem[typeLens];
Show[Table[
baseSurf=params[[ii]];
Switch[Length[baseSurf[[2]]],
0,
Graphics3D[{(*colors[[typeLenRepElem[[ii]]]]*)Purple,Point[baseSurf[[1]]]}],
_,
plotParamPiece[baseSurf,vars,PlotStyle->colors[[typeLenRepElem[[ii]]]]]
]
,{ii,Length[params]}],PlotRange->All]
]

boundaryAtlasPolarParamsReduced[atlas_,vars_,ncList_]:=Module[{normalCones,generators},
Inner[Function[{setInclusionIx,edge},Table[
normalCones=ncList[[setInclusionIx]];
(* I want The convex hull of this: *)
generators=normalCones/.Thread[vars->param[[1]]]//Simplify;
Switch[Length[generators],
1,
{generators[[1]],param[[2]],param[[3]],{{0,1}}},
2,
{s generators[[1]]+(1-s)generators[[2]],Join[param[[2]],{s}],Join[param[[3]],{{0,1}}]},
_,
param(*Polygon[generators]*)(* Need to generalize above *)
]
,{param,edge}]],atlas[[;;,atlasCol["regionIxs"]]],atlas[[;;,atlasCol["paramsReduced"]]],List]
]


(* ::Input:: *)
(*cnd=({x,y,z} . {x,y,z}<=1/.x->x-1/2)&&({x,y,z} . {x,y,z}<=1/.x->x+1/2)&&({x,y,z} . {x,y,z}<=1/.z->z+1/2)&&({x,y,z} . {x,y,z}<=1/.z->z-1/2)*)
(*vars={x,y,z}*)
(*atlas=boundaryAtlas[cnd,vars];*)
(*testPoint=First[vars/.FindInstance[atlas[[5,atlasCol["simpleCnd"]]],vars]]*)
(*boundaryAtlasLookup[atlas,vars,testPoint]*)
(*boundaryAtlasPlot[atlas,vars]*)


(* ::Input:: *)
(*F=initializeSet[cnd,vars]*)
(*ncList=F["ncList"]*)


(* ::Input:: *)
(*ncList*)


(* ::Input:: *)
(*atlas//MatrixForm;*)
(*(* boundaryAtlasPolarParam *)*)
(*newParamsReduced=Inner[Function[{setInclusionIx,edge},Table[*)
(*normalCones=ncList[[setInclusionIx]];*)
(*(* I want The convex hull of this: *)*)
(*generators=normalCones/.Thread[F["vars"]->param[[1]]]//Simplify;*)
(*Switch[Length[generators],*)
(*1,*)
(*{generators[[1]],param[[2]],param[[3]],{{0,1}}},*)
(*2,*)
(*polarSurf={s generators[[1]]+(1-s)generators[[2]],Join[param[[2]],{s}],Join[param[[3]],{{0,1}}]};*)
(*polarSurf,*)
(*_,*)
(*param(*Polygon[generators]*)*)
(*]*)
(*,{param,edge}]],atlas[[;;,1]],atlas[[;;,4]],List];*)
(**)
(*(*Show[plotParamPiece[#,F["vars"]]&/@Flatten[newParamsReduced,1],PlotRange->All]*)*)
(*boundaryAtlasPlot[Transpose@ConstantArray[newParamsReduced,4],F["vars"]]*)


(* ::Input:: *)
(*newParamsReduced // MatrixForm*)


(* ::Input:: *)
(*params=Flatten[atlas[[;;,4]],1];*)
(*Show[Table[*)
(*baseSurf=params[[ii]];*)
(*normalCones=ncList[[Flatten@Position[setInclusionQ[[ii]],True]]];*)
(*(* I want The convex hull of this: *)*)
(*generators=normalCones/.Thread[f1["vars"]->baseSurf[[1]]]//Simplify;*)
(*Switch[Length[generators],*)
(*1,*)
(*polarSurf={generators[[1]],baseSurf[[2]],baseSurf[[3]],{{0,1}}};*)
(*plotParamPiece[polarSurf,f1["vars"],PlotStyle->colors[[typeLenRepElem[[ii]]]]],*)
(*2,*)
(*polarSurf={s generators[[1]]+(1-s)generators[[2]],Join[baseSurf[[2]],{s}],Join[baseSurf[[3]],{{0,1}}]};*)
(*Echo[polarSurf];*)
(*plotParamPiece[polarSurf,f1["vars"],PlotStyle->colors[[typeLenRepElem[[ii]]]]],*)
(*_,*)
(*Graphics3D[{colors[[typeLenRepElem[[ii]]]],Polygon[generators[[{1,3,2,4}]]]}]*)
(*]*)
(*,{ii,Length[params]}],PlotRange->All,ViewPoint->{1,2,1}]*)


(* ::Input:: *)
(*testPoint={0,0,1/2}*)
(*subsetIx=LengthWhile[cndIxParamTuples[[;;,2]],!trep[#,vars,testPoint]&]+1*)
(*Assert[subsetIx<=Length[cndIxParamTuples]](* Not a boundary point *)*)
(*paramIx=LengthWhile[cndIxParamTuples[[subsetIx,3]],!trep[#,vars,testPoint]&]+1*)
(*Assert[paramIx<=Length[cndIxParamTuples]](* Could not find suitable param? Should not happen ... *)*)
(*paramVals=trep[cndIxParamTuples[[subsetIx,4]][[paramIx]][[2]],vars,testPoint]*)


(* ::Input:: *)
(*reducedParamVerifier[redParam_,vars_,testPoint_]:=With[{cnd=Fold[And,#2[[1]]<=#1<=#2[[2]]&@@@Transpose[redParam[[{2,3}]]]]},*)
(*trep[cnd,vars,testPoint]*)
(*]*)


(* ::Input:: *)
(*typeLenRepElem=Flatten[ConstantArray[#,#2]&@@@Transpose@{Range[Length[typeLens]],typeLens}];*)
(*colors={Orange,Blue,Purple};*)
(**)
(*Show[Table[*)
(*baseSurf=params[[ii]];*)
(*normalCones=ncList[[Flatten@Position[setInclusionQ[[ii]],True]]];*)
(*(* I want The convex hull of this: *)*)
(*generators=normalCones/.Thread[f1["vars"]->baseSurf[[1]]]//Simplify;*)
(*Switch[Length[generators],*)
(*1,*)
(*polarSurf={generators[[1]],baseSurf[[2]],baseSurf[[3]],{{0,1}}};*)
(*plotParamPiece[polarSurf,f1["vars"],PlotStyle->colors[[typeLenRepElem[[ii]]]]],*)
(*2,*)
(*polarSurf={s generators[[1]]+(1-s)generators[[2]],Join[baseSurf[[2]],{s}],Join[baseSurf[[3]],{{0,1}}]};*)
(*Echo[polarSurf];*)
(*plotParamPiece[polarSurf,f1["vars"],PlotStyle->colors[[typeLenRepElem[[ii]]]]],*)
(*_,*)
(*Graphics3D[{colors[[typeLenRepElem[[ii]]]],Polygon[generators[[{1,3,2,4}]]]}]*)
(*]*)
(*,{ii,Length[params]}],PlotRange->All,ViewPoint->{1,2,1}]*)


(* ::Input:: *)
(*polarBoundaryAtlas[]*)


(* ::Input:: *)
(*f=initializeSet[x^2<=1,{x,y}]*)
(*f["nan"]*)
(*plot[f,5]*)


(* ::Input:: *)
(*Format[optIntSet[id_]]:=Module[{},id]*)
(*f=initializeSet[And[x^2<=1,y<=1],{x,y}]*)
(*f["nan"]*)
(*plot[f]*)


(* ::Input:: *)
(**)


(* ::Section:: *)
(*UI Development*)


(* ::Input:: *)
(*OpenerView[{Plus,x+y+z},True]*)


(* ::Subsection:: *)
(*v1*)


(* ::Input:: *)
(*optFun[ix_]["init","displayMode"]:="full"*)
(*Format[optFun[id_]]:=Module[{hlRules,f=optFun[id],d0={}(*KeyDrop[optFun[id]["data"],"parent"]*)(*optFun[id]["data"]*)},*)
(*Switch[f["displayMode"],*)
(*"full",*)
(*DynamicModule[{s=False},{OpenerView[{Plus,Dynamic@Refresh[If[s,optFun[id]["data"]],TrackedSymbols:>{s}]},Dynamic[s]],Checkbox[Dynamic[s]]}](*;*)
(*hlRules=#->Style[#,FontColor->Blue,FontWeight->Medium]&/@f["vars"];*)
(*Tooltip[Panel[Magnify[f["expr"]/.hlRules//TraditionalForm,1.25],FrameMargins->0,Background->Lighter[Gray,0.95]],d0]*),*)
(*"name",*)
(*Tooltip[Magnify[Style[f["name"],FontColor->Red,FontWeight->Medium]//TraditionalForm,1.25],d0]*)
(*]];*)
(*formatExpr[optFun[id_]]:=Module[{hlRules,f=optFun[id]},*)
(*hlRules=#->Style[#,FontColor->Blue,FontWeight->Medium]&/@f["vars"];*)
(*Tooltip[Panel[Magnify[f["expr"]/.hlRules//TraditionalForm,1.25],FrameMargins->0,Background->Lighter[Gray,0.95]],*)
(*{optFun,id,optFun[id]["name"]}]*)
(*]*)
(*formatName[optFun[id_]]:=Style[optFun[id]["name"],FontColor->Blue,FontWeight->Medium]*)
(*Format[optFun[id_]]:=DynamicModule[{x={},f=optFun[id]},*)
(*Dynamic[Refresh[DynamicModule[{usingNames=MemberQ[x,1],showingPanel=MemberQ[x,2],nameDisplay,selectorPanel},*)
(*nameDisplay=If[usingNames,formatName[f],formatExpr[f]];*)
(*selectorPanel=Panel[Row[{nameDisplay,TogglerBar[Dynamic[x],{1->If[usingNames,">","<"],2->If[showingPanel,"\[FilledUpTriangle]","\[FilledDownTriangle]"]}]},"  "],FrameMargins->0];*)
(*Column[{*)
(*Mouseover[If[showingPanel,selectorPanel,nameDisplay],selectorPanel],*)
(*Sequence@@If[!showingPanel,{},{Panel[*)
(*Dataset[f["data"]]*)
(*]}]*)
(*}]*)
(*],TrackedSymbols:>{x}]]*)
(*]*)
(*Clear[x]*)
(*Format[optMaxFun[id_]]:=Module[{f=optMaxFun[id],c=optMaxFun[id]["children"]},CirclePlus@@c]*)
(*f=initializeFunction[Max[x^2+ Sqrt[x y]+y^4,x],{x,y}]*)
(*f["nan"]*)


(* ::Subsection:: *)
(*v2*)


(* ::Input:: *)
(*Toggler[False,{True,False}]*)


(* ::Input:: *)
(*Button[Defer[Sort[\[SelectionPlaceholder]]],None,BaseStyle->"Evaluate"]*)


(* ::Input:: *)
(*Sort[\[SelectionPlaceholder]]*)


(* ::Input:: *)
(*optFun[ix_]["init","displayMode"]:="full"*)
(*Format[optFun[id_]]:=Module[{hlRules,f=optFun[id],d0={}(*KeyDrop[optFun[id]["data"],"parent"]*)(*optFun[id]["data"]*)},*)
(*Switch[f["displayMode"],*)
(*"full",*)
(*DynamicModule[{s=False},{OpenerView[{Plus,Dynamic@Refresh[If[s,optFun[id]["data"]],TrackedSymbols:>{s}]},Dynamic[s]],Checkbox[Dynamic[s]]}](*;*)
(*hlRules=#->Style[#,FontColor->Blue,FontWeight->Medium]&/@f["vars"];*)
(*Tooltip[Panel[Magnify[f["expr"]/.hlRules//TraditionalForm,1.25],FrameMargins->0,Background->Lighter[Gray,0.95]],d0]*),*)
(*"name",*)
(*Tooltip[Magnify[Style[f["name"],FontColor->Red,FontWeight->Medium]//TraditionalForm,1.25],d0]*)
(*]];*)
(*formatExpr[optFun[id_]]:=Module[{hlRules,f=optFun[id]},*)
(*hlRules=#->Style[#,FontColor->Blue,FontWeight->Medium]&/@f["vars"];*)
(*Panel[Magnify[f["expr"]/.hlRules//TraditionalForm,1.25],FrameMargins->0,Background->Lighter[Gray,0.95]]*)
(*]*)
(*formatExpr[optMaxFun[id_]]:=Module[{f=optMaxFun[id],c=optMaxFun[id]["children"]},*)
(*Panel[CirclePlus@@c]*)
(*]*)
(*formatName[(f_optFun|f_optMaxFun)]:=Style[f["name"],FontColor->Blue,FontWeight->Medium]*)
(*(*(h_optFun|h_optMaxFun|h_optSet|h_optIntSet)*)*)
(*dynamicOptFormater[type_[id_]]:=DynamicModule[{x={},f=type[id]},*)
(*Dynamic[Refresh[DynamicModule[{usingNames=MemberQ[x,1],showingPanel=MemberQ[x,2],nameDisplay,selectorPanel},*)
(*nameDisplay=If[usingNames,formatName[f],formatExpr[f]];*)
(*selectorPanel=Tooltip[Panel[Row[{Button[nameDisplay,If[showingPanel,x=DeleteCases[x,2],x=Append[x,2]],Appearance->"Frameless"],TogglerBar[Dynamic[x],{1->If[usingNames,">","<"],2->If[showingPanel,"\[FilledUpTriangle]","\[FilledDownTriangle]"]}]},"  "],FrameMargins->0],*)
(*{type,id,type[id]["name"]}];*)
(*Column[{*)
(*Mouseover[If[showingPanel,selectorPanel,nameDisplay],selectorPanel],*)
(*Sequence@@If[!showingPanel,{},{Panel[*)
(*Dataset[f["data"]]*)
(*]}]*)
(*}]*)
(*],TrackedSymbols:>{x}]]*)
(*]*)
(*Format[optFun[id_]]:=dynamicOptFormater[optFun[id]]*)
(*Format[optMaxFun[id_]]:=dynamicOptFormater[optMaxFun[id]]*)
(*(*Format[optFun[ix_]]:=myFormat[optFun[ix]]*)
(*Format[optMaxFun[ix_]]:=myFormat[optMaxFun[ix]]*)*)
(*(* There should just be a switch statement that overwrite formatters *)*)
(*Clear[x]*)
(*(*Format[optMaxFun[id_]]:=Module[{f=optMaxFun[id],c=optMaxFun[id]["children"]},CirclePlus@@c]*)*)
(*f=initializeFunction[Max[x^2+ Sqrt[x y]+y^4,x],{x,y}]*)
(*f["nan"]*)


(* ::Input:: *)
(*Mouseover[off,on]*)


(* ::Input:: *)
(*DynamicModule[{x=1},{Slider[Dynamic[x]],Dynamic[x=Max[0,x-0.01]]}]*)


(* ::Input:: *)
(**)


(* ::Input:: *)
(*Dynamic[Refresh[Magnify[TogglerBar[Dynamic[$CellContext`x$$], {1 -> If[MemberQ[$CellContext`x$$, 1], "<", ">"], 2 -> If[MemberQ[$CellContext`x$$, 2], "\[FilledUpTriangle]", "\[FilledDownTriangle]"]}, Appearance -> "Vertical"], 0.5], TrackedSymbols :> {$CellContext`x$$}], ImageSizeCache -> {13., {9.853613239200786, 12.146386760799214`}}]//FullForm*)


(* ::Input:: *)
(*DynamicModule[{s=False},{OpenerView[{Plus,Dynamic@Refresh[If[s,Assert[False];s],TrackedSymbols:>{s}]},Dynamic[s]],Checkbox[Dynamic[s]]}]*)


(* ::Input:: *)
(*FlipView[{40!,Plot[Sin[x],{x,0,2 Pi}],Factor[x^14-1]}]*)


(* ::Subsection:: *)
(*v3*)


(* ::Input:: *)
(*setOptFormat["dynamic"]*)
(*f=initializeFunction[Max[x^2+ Sqrt[x y]+y^4,x],{x,y}]*)
(*f["convexity"]*)
(*%[[1]]*)


(* ::Input:: *)
(*setOptFormat["expr"]*)


(* ::Input:: *)
(*setOptFormat["dynamic"]*)
(*f=initializeSet[2x^2<=1&&2y^2<=1,{x,y}]*)
(*f["gauge"]*)
(*f["data"]*)
(*objRelationGraph[f]*)


(* ::Input::Initialization:: *)
freeOptQ[expr_]:=And@@(FreeQ[expr,#]&/@{optFun,optMaxFun,optSet,optIntSet})
getPatterns[expr_,pat_]:=Last@Reap[expr/. a:pat:>Sow[a],_,Sequence@@#2&](* cases does not include head, even at level 0 *)
optCases[expr_]:=Flatten[getPatterns[expr,#]&/@{_optFun,_optMaxFun,_optSet,_optIntSet}]


(* ::Input:: *)
(*Cases[1,_Integer,0]*)


(* ::Input::Initialization:: *)
Options[objRelationGraph]={TrivialEdges->True};
objRelationGraph[f_,OptionsPattern[]]:=Block[{g},
visitedObjs={};
objQueue={f};
edgeList={};

While[Length[objQueue]>0,
Block[{ff=objQueue[[1]]},
relationalCandidates=Flatten[KeyValueMap[
With[{cases=optCases[#2]},If[Length[cases]>0,Function[{case},{ff,case,#1}]/@cases,Missing[]]]&,
ff["data"]
]/.Missing[]->Sequence[],1];
edgeList=Join[edgeList,DirectedEdge@@@relationalCandidates];
visitedObjs=Join[visitedObjs,{ff}];
objQueue=DeleteCases[objQueue,ff];
objQueue=Join[objQueue,Complement[relationalCandidates[[;;,2]],visitedObjs]];
]
];

g=Graph[edgeList,VertexLabels->"Name",EdgeLabels->"EdgeTag"];
If[Not@OptionValue[TrivialEdges],g=EdgeDelete[g,EdgeList[g][[Flatten@Position[SameQ[{},#]&/@StringCases[EdgeTags[g],___~~"Of"],False]]]]];
g
]


(* ::Input:: *)
(*f=initializeFunction[x^2+1,{x}]*)
(*f["epi"]["polar"]["polar"]["expr"]*)
(*objRelationGraph[f,TrivialEdges->False]*)


(* ::Input::Initialization:: *)
functionList[context_String:"Global`"]:=TableForm@Sort[HoldForm@@@Flatten[(ToExpression[#,InputForm,DownValues]&/@Names[context<>"*"])[[All,All,1]]]]


(* ::Input:: *)
(*visitedObjs={};*)
(*objQueue={f};*)
(*edgeList={};*)
(**)
(*While[Length[objQueue]>0,*)
(*Block[{f=objQueue[[1]]},*)
(*relationalCandidates=Flatten[KeyValueMap[*)
(*With[{cases=optCases[#2]},If[Length[cases]>0,Function[{case},{f,case,#1}]/@cases,Missing[]]]&,*)
(*ff["data"]*)
(*]/.Missing[]->Sequence[],1];*)
(*edgeList=Join[edgeList,DirectedEdge@@@relationalCandidates];*)
(*visitedObjs=Join[visitedObjs,{ff}];*)
(*objQueue=DeleteCases[objQueue,ff];*)
(*objQueue=Join[objQueue,Complement[relationalCandidates[[;;,2]],visitedObjs]];*)
(*]*)
(*];*)
(**)
(*Graph[edgeList,VertexLabels->"Name",EdgeLabels->"EdgeTag"]*)


(* ::Input:: *)
(*newObjQ=!MemberQ[#[[3]],visitedObjs]&/@relationalCandidates(* I don't know how much this matters *)*)


(* ::Input:: *)
(*Hold[1+1]*)


(* ::Input:: *)
(*First@First@Hold[False]*)


(* ::Section:: *)
(*Opt Classes*)


Clear[optObj, optFun, optSet, optISet, optPSet, optDSet]


(* ::Input::Initialization:: *)
DEBUG = False;


(* ::Subsection:: *)
(*optObj*)


(* ::Code::Initialization::Bold:: *)
(* basic stateful object that has inheritance *)
optObj[data_Association] := With[{ix = Unique[]},
    optObj[ix]["data"] = data;
    optObj[ix]
    ]
optObj[ix_]["get", prop_] := Lookup[optObj[ix]["data"], prop,
      With[{newProp = optObj[ix]["init", prop]},If[(*Not[First@newProp==="init"]*)True,AppendTo[optObj[ix]["data"], prop -> newProp]]]; 
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
    If[SameQ[Head@varsTMP, Symbol],
      varsTMP = {vars}
      ];
    If[SameQ[Head@exprTMP, List],
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


(* ::Subsection:: *)
(*optFun*)


(* ::Input::Initialization:: *)
DownValues[optFun]=ReplaceRepeated[DownValues[optObj],optObj->optFun];
SubValues[optFun]=ReplaceRepeated[SubValues[optObj],optObj->optFun];
sub[optFun[ix_],val_]:=optObj[ix]["expr"]/.Thread[optFun[ix]["vars"]->val]
optFun[ix_]["init","verbose"]:=DEBUG
optFun[ix_]["init","name"]:=Subscript[\[FormalF],ix]


(* ::Input::Initialization:: *)
optFun[ix_]["init","displayMode"]:="full"
(*Format[optFun[id_]]:=Module[{hlRules,f=optFun[id],d0={}(*KeyDrop[optFun[id]["data"],"parent"]*)},
Switch[f["displayMode"],
"full",
hlRules=#->Style[#,FontColor->Blue,FontWeight->Medium]&/@f["vars"];
Tooltip[Panel[Magnify[f["expr"]/.hlRules//TraditionalForm,1.25],FrameMargins->0,Background->Lighter[Gray,0.95]],d0],
"name",
Tooltip[Magnify[Style[f["name"],FontColor->Red,FontWeight->Medium]//TraditionalForm,1.25],d0]
]];*)


(* ::Input::Initialization:: *)
plotBoundsParser[vars_,bounds_:{}]:=Module[{b=bounds,nVars},nVars=Length[vars];
(*infer bounds*)
If[SameQ[b,{}],b=1];
(*default to unit box*)
If[NumberQ[b],b=b*{-1,1}];
If[Length[b]==2&&NumberQ[b[[1]]],b=Table[b,{nVars}]];
b=Join[List/@vars,b,2]]
plot[optFun[ix_],bounds_:{},varargin___]:=Module[{f=optFun[ix],b=plotBoundsParser[optFun[ix]["vars"],bounds]},
(*TODO: make manipulate if there are parameters*)
Switch[Length[f["vars"]],
1,Plot[f["expr"]//cvxReduce,Evaluate[Sequence@@b],varargin],
2,Plot3D[f["expr"]//cvxReduce,Evaluate[Sequence@@b],varargin],
_,Missing[]]
]
cplot[optFun[ix_],bounds_:{},varargin___]:=Module[{f=optFun[ix],b=plotBoundsParser[optFun[ix]["vars"],bounds]},
(*TODO: make manipulate if there are parameters*)
Switch[Length[f["vars"]],
1,Missing[],
2,ContourPlot[f["expr"]//cvxReduce,Evaluate[Sequence@@b],varargin],
3,ContourPlot3D[f["expr"]//cvxReduce,Evaluate[Sequence@@b],varargin],_,Missing[]]
]


(* ::Subsubsection:: *)
(*relation to optMaxFun*)


(* ::Input::Initialization:: *)
optFun[ix_]["init","parent"]:=Null


(* ::Subsubsection:: *)
(*related sets*)


(* ::Input::Initialization:: *)
optFun[ix_]["init","lev"]:=Module[{f=optFun[ix],d=optFun[ix]["data"],dObj},
dObj=initializeSet@@lev[d["expr"],d["vars"],1];

If[!SameQ[d["convexity"],Indeterminate],AppendTo[dObj["data"],"convex"->True]];
If[trep[d["expr"],d["vars"],ConstantArray[0,Length[d["vars"]]]]==0&&dObj["contains0"],AppendTo[dObj["data"],"gauge"->f]];(* 3.3.11 *)

dObj
]


(* ::Subsubsection:: *)
(*convexity properties*)


(* ::Input::Initialization:: *)
optFun[ix_]["init","convexity"]:=With[{d=optFun[ix]["data"]},FunctionConvexity[{d["expr"],d["cnd"]},d["vars"]]]
optFun[ix_]["init","convex"]:=optFun[ix]["data"]["convexity"]===1
optFun[ix_]["init","domain"]:=With[{d=optFun[ix]["data"]},initializeSet@@dom[d["expr"],d["vars"]]]
optFun[ix_]["init","epi"]:=With[{d=optFun[ix]["data"]},initializeSet@@epi[d["expr"],d["vars"]]]


(* ::Subsection:: *)
(*optMaxFun*)


(* ::Input::Initialization:: *)
DownValues[optMaxFun]=ReplaceRepeated[DownValues[optObj],optObj->optMaxFun];
SubValues[optMaxFun]=ReplaceRepeated[SubValues[optObj],optObj->optMaxFun];
sub[optMaxFun[ix_],val_]:=optMaxFun[ix]["expr"]/.Thread[optMaxFun[ix]["vars"]->val]
optMaxFun[ix_]["init","verbose"]:=DEBUG


(* ::Input::Initialization:: *)
optMaxFun[ix_]["init","children"]:=Module[{parts=optMaxFun[ix]["expr"]/.Max->List,children,myName},
children=If[Head[#]===optFun,#,optFun[#,optMaxFun[ix]["vars"]]]&/@parts;
AppendTo[optMaxFun[ix]["data"],"expr"->Max@@(#["expr"]&/@children)];(* inheritance is kind of tricky when *)
myName=optMaxFun[ix]["name"];
MapIndexed[AppendTo[#1["data"],"name"->Subscript[myName,#2[[1]]]/.Subscript[a_,Subscript[b_,c_]]:>Subscript[a,{b,c}]]&,children];
Map[AppendTo[#1["data"],"parent"->optMaxFun[ix]]&,children];
(*Map[AppendTo[#1["data"],"displayMode"->"name"]&,children];*)
children
]
optMaxFun[ix_]["init","name"]:=Subscript[\[FormalF],ix]


(* ::Input::Initialization:: *)
  (*Format[optMaxFun[id_]] := Module[{hlRules, d0 = KeyDrop[optMaxFun[id]["data"],"children"], c = optMaxFun[id]["data"]["children"]},
  Tooltip[Panel[c/.List->CirclePlus]//TraditionalForm,d0]]*)


(* ::Input::Initialization:: *)
optMaxFun[ix_]["init","epi"]:=Module[{c=optMaxFun[ix]["children"]},initializeSet[Fold[And,#["epi"]["expr"]&/@c],c[[1]]["epi"]["vars"],Name->epi[optMaxFun[ix]["name"]]]]


(* ::Input::Initialization:: *)
plot[optMaxFun[ix_],bounds_:{},varargin___]:=Module[{f=optMaxFun[ix],b=plotBoundsParser[optMaxFun[ix]["vars"],bounds]},
(*TODO: make manipulate if there are parameters*)
Switch[Length[f["vars"]],
1,Plot[f["expr"]//cvxReduce,Evaluate[Sequence@@b],varargin],
2,Plot3D[f["expr"]//cvxReduce,Evaluate[Sequence@@b],varargin],
_,Missing[]]
]
cplot[optMaxFun[ix_],bounds_:{},varargin___]:=Module[{f=optMaxFun[ix],b=plotBoundsParser[optMaxFun[ix]["vars"],bounds]},
(*TODO: make manipulate if there are parameters*)
Switch[Length[f["vars"]],
1,Missing[],
2,ContourPlot[f["expr"]//cvxReduce,Evaluate[Sequence@@b],varargin],
3,ContourPlot3D[f["expr"]//cvxReduce,Evaluate[Sequence@@b],varargin],_,Missing[]]
]


(* ::Subsection:: *)
(*optSet*)


(* ::Input::Initialization:: *)
DownValues[optSet]=ReplaceRepeated[DownValues[optObj],optObj->optSet];
SubValues[optSet]=ReplaceRepeated[SubValues[optObj],optObj->optSet];

sub[optSet[ix_],val_]:=optSet[ix]["expr"]/.Thread[optSet[ix]["vars"]->val]
optID[optSet[ix_]] := ix;
isComputed[optSet[ix_], key_] := KeyExistsQ[optSet[ix]["data"], key];
nVars[optSet[ix_]] := Length[optSet[ix]["vars"]]
optSet[ix_]["init","verbose"]:=DEBUG


(* ::Input::Initialization:: *)
(*Format[optSet[id_]]:=Module[{hlRules,f=optSet[id],d0={}(*KeyDrop[optSet[id]["data"],"parent"]*)},
Switch[f["displayMode"],
"full",
hlRules=#->Style[#,FontColor->Blue,FontWeight->Medium]&/@f["vars"];
Tooltip[Panel[Magnify[f["expr"]/.hlRules//TraditionalForm,1.25],FrameMargins->0],d0],
"name",
Tooltip[Magnify[Style[f["name"],FontColor->Purple,FontWeight->Medium]//TraditionalForm,1.25],d0]
]];*)


(* ::Input::Initialization:: *)
optSet[ix_]["init","name"]:=Subscript[C,ix]
optSet[ix_]["init","displayMode"]:="full"


(* ::Input::Initialization:: *)
plot[optSet[ix_],bounds_:{},varargin___]:=Module[{f=optSet[ix],b=plotBoundsParser[optSet[ix]["vars"],bounds]},
(*TODO: make manipulate if there are parameters*)
Switch[Length[f["vars"]],
2,RegionPlot[f["expr"]//cvxReduce,Evaluate[Sequence@@b],varargin],
3,RegionPlot3D[f["expr"]//cvxReduce,Evaluate[Sequence@@b],varargin],
_,Missing[]]
]


(* ::Subsubsection:: *)
(*relation to optIntSet*)


(* ::Input::Initialization:: *)
optISet[ix_]["init","parent"]:=Null


(* ::Subsubsection:: *)
(*convexity properties*)


(* ::Input::Initialization:: *)
optSet[ix_]["init","name"]:=Subscript[C,ix]
optSet[ix_]["init","displayMode"]:="full"
optSet[ix_]["init","contains0"]:=With[{f=optSet[ix]},Reduce[Implies[f["cnd"],Reduce[sub[f,Table[0,Length[f["vars"]]]]]],f["vars"],Reals]]
optSet[ix_]["init","bounded"]:=With[{f=optSet[ix]},Reduce[Implies[f["cnd"],bounded[cvxReduce[f["expr"]],f["vars"]]],f["vars"],Reals]]


(* ::Input:: *)
(**)


(* ::Subsection:: *)
(*optIntSet*)


(* ::Input::Initialization:: *)
DownValues[optIntSet]=ReplaceRepeated[DownValues[optObj],optObj->optIntSet];
SubValues[optIntSet]=ReplaceRepeated[SubValues[optObj],optObj->optIntSet];
sub[optIntSet[ix_],val_]:=optIntSet[ix]["expr"]/. Thread[optIntSet[ix]["vars"]->val]
optIntSet[ix_]["init","verbose"]:=DEBUG


(* ::Input::Initialization:: *)
(*Format[optIntSet[id_]]:=Module[{hlRules,d0=optIntSet[id]["data"],c=optIntSet[id]["data"]["children"]},Tooltip[Panel[c/. List->And]//TraditionalForm,d0]]*)


(* ::Input::Initialization:: *)
optIntSet[ix_]["init","children"]:=Module[{parts=optIntSet[ix]["expr"]/.And->List,children,myName},
Assert[AllTrue[parts,Head[#]===LessEqual&]];
children=optSet[#[[1]]-#[[2]]+1<=1,optIntSet[ix]["vars"]]&/@parts;
myName=optIntSet[ix]["name"];
MapIndexed[AppendTo[#1["data"],"name"->Subscript[myName,#2[[1]]]/.Subscript[a_,Subscript[b_,c_]]:>Subscript[a,{b,c}]]&,children];
Map[AppendTo[#1["data"],"parent"->optIntSet[ix]]&,children];
(*Map[AppendTo[#1["data"],"displayMode"->"name"]&,children];*)
children
]
optIntSet[ix_]["init","name"]:=Subscript[C,ix]


(* ::Input::Initialization:: *)
plot[optIntSet[ix_],bounds_:{},varargin___]:=Module[{f=optIntSet[ix],b=plotBoundsParser[optIntSet[ix]["vars"],bounds]},
(*TODO: make manipulate if there are parameters*)
Switch[Length[f["vars"]],
2,RegionPlot[f["expr"]//cvxReduce,Evaluate[Sequence@@b],varargin],
3,RegionPlot3D[f["expr"]//cvxReduce,Evaluate[Sequence@@b],varargin],
_,Missing[]]
]
boundaryPlot[optIntSet[ix_],varargin___]:=Module[{f=optIntSet[ix]},
(*TODO: make manipulate if there are parameters*)
boundaryAtlasPlot[f["boundaryAtlas"],f["vars"]]
]


(* ::Subsubsection:: *)
(*Properties From Children*)


(* ::Input::Initialization:: *)
optIntSet[ix_]["init","contains0"]:=Module[{c=optIntSet[ix]["children"]},Reduce[And@@Map[#["contains0"]&,c]]]
optIntSet[ix_]["init","bounded"]:=Module[{c=optIntSet[ix]["children"]},
If[Reduce[And@@Map[#["bounded"]&,c]]===True,True,
With[{f=optIntSet[ix]},bounded[f["expr"],f["vars"]]]
]]
optIntSet[ix_]["init","gauge"]:=Module[{c=optIntSet[ix]["children"],d=optIntSet[ix]["data"]},
initializeFunction[Max[Map[#["gauge"]&,c]],d["vars"]]
]
optIntSet[ix_]["init","ncList"]:=Module[{c=optIntSet[ix]["children"],d=optIntSet[ix]["data"]},
Map[#["normalizedNormalCone"]&,c]
]


(* ::Subsubsection:: *)
(*Manual Properties*)


(* ::Input::Initialization:: *)
optIntSet[ix_]["init","boundaryAtlas"]:=Module[{obj=optIntSet[ix]},boundaryAtlas[obj["expr"],obj["vars"]]]


(* ::Subsubsection:: *)
(*Functions*)


(* ::Input::Initialization:: *)
project[optIntSet[ix_],x_]:=x/sub[optIntSet[ix]["gauge"],x]


(* ::Subsection:: *)
(*Fancy Input Forms*)


(* ::Input::Initialization:: *)
BoundaryConditions[f_optSet]:=f["expr"]
NormalizedNormalCone[f_optSet]:=Function[Evaluate[f["vars"]],f["NormalizedNormalCone"]]
Subscript[\!\(\*OverscriptBox[\(\[ScriptCapitalN]\), \(^\)]\), f_optSet]:=NormalizedNormalCone[f]
Polar[f_optSet]:=f["polar"]
f_optSet^\[Degree]:=Polar[f]
Gauge[f_optSet]:=Function[Evaluate[f["vars"]],f["gauge"]]
Subscript[\[Gamma], f_optSet]:=Gauge[f]


(* ::Section:: *)
(*Opt Classes Tests*)


(* ::Input::Initialization:: *)
Options[initializeFunction]={Conditions->True,Name->Automatic}
initializeFunction[{f_,cnds_},vars_,OptionsPattern[]]:=initializeFunction[f,vars,
Sequence@@(
If[#1===Conditions,
#1->cnds&&Element[Alternatives@@vars,Reals]&&OptionValue[#1],
#1->OptionValue[#1]
]&@@@Options[initializeFunction]
)]
initializeFunction[f_,vars_,OptionsPattern[]]:=Module[{f0},
f0=optFun[{f,OptionValue[Conditions]},vars];
If[Not[OptionValue[Name]===Automatic],AppendTo[f0["data"], "name"->OptionValue[Name]]];
f0
]
initializeFunction[f_Max,vars_,OptionsPattern[]]:=Module[{F0},
F0=optMaxFun[{f,OptionValue[Conditions]},vars];
If[Not[OptionValue[Name]===Automatic],AppendTo[F0["data"], "name"->OptionValue[Name]]];
F0["children"];
F0
]



(* ::Subsection:: *)
(*intersection*)


(* ::Input:: *)
(*initializeSet[{x,y} . {x,y}<=1,{x,y}]*)


(* ::Input::Initialization:: *)
Options[initializeSet]={Conditions->True,Name->Automatic}
initializeSet[{f_,cnds_},vars_,OptionsPattern[]]:=initializeSet[f,vars,
Sequence@@(
If[#1===Conditions,
#1->cnds&&Element[Alternatives@@vars,Reals]&&OptionValue[#1],
#1->OptionValue[#1]
]&@@@Options[initializeSet]
)]

initializeSet[f_GreaterEqual,vars_,OptionsPattern[]]:=initializeSet[-f[[2]]<=f[[1]],vars,Sequence@@(#1->OptionValue[#1]&@@@Options[initializeSet])]
initializeSet[f_LessEqual,vars_,OptionsPattern[]]:=Module[{f0},
f0=optSet[{f,OptionValue[Conditions]},vars];
If[Not[OptionValue[Name]===Automatic],AppendTo[f0["data"], "name"->OptionValue[Name]]];
f0
]
initializeSet[f_And,vars_,OptionsPattern[]]:=Module[{F0},
F0=optIntSet[{f,OptionValue[Conditions]},vars];
If[Not[OptionValue[Name]===Automatic],AppendTo[F0["data"], "name"->OptionValue[Name]]];
F0["children"];
F0
]



(* ::Input:: *)
(*f1=optSet[{x,y} . {x,y}<=1,{x,y}]*)
(*f1["name"]*)


(* ::Input:: *)
(*f1=initializeSet[{x,y} . {x,y}<=1,{x,y},Name->F]*)
(*f1["name"]*)


(* ::Input:: *)
(**)


(* ::Input:: *)
(*Reduce[Implies[True,x]]*)


(* ::Input::Initialization:: *)
optSet[ix_]["init","support"]:=Module[{f=optSet[ix],d=optSet[ix]["data"],sol,dObj,polarReccCnds},
Echo[{FreeQ[d["expr"],indicator],f["bounded"]},{f["name"],"Support"}];

If[FreeQ[d["expr"],indicator]||f["bounded"]===True,

If[!f["bounded"],

(*If[isComputed[f,"gauge"],Echo[f["gauge"]]];*)

If[f["contains0"]&&isComputed[f,"gauge"],
(* Basu, A. 3.3.11 *)
polarReccCnds=polar[Reduce[f["gauge"]["expr"]==0//cvxReduce,f["gauge"]["vars"],Reals],f["gauge"]["vars"]];
If[f["verbose"],Echo[StringForm["polarReccCnds `` computed using gauge",polarReccCnds],{f["name"],"Support"}]];
,
polarReccCnds=polarRecc[d["expr"]//cvxReduce,d["vars"]];
If[f["verbose"],Echo[StringForm["polarReccCnds `` computed directly",polarReccCnds],{f["name"],"Support"}]];
];,
polarReccCnds={True,{}}
];

sol=simpleSupport[d["expr"]/.indicator[_]->0,d["vars"],polarReccCnds[[1]]&&d["cnd"]];

(*Echo[{polarReccCnds}];*)
sol=Assuming[polarReccCnds[[1]]&&d["cnd"],Simplify[sol]]+indicator[polarReccCnds[[1]]]

If[!FreeQ[sol,formalVector[d["vars"]][[1]]],
If[f["verbose"],Echo[StringForm["Support computation of `` using stationarySupport failed: ``",{d["expr"]/.indicator[_]->0,d["vars"]},sol],{f["name"],"Support"}]];
(* TODO: better control flow *)
sol=support[d["expr"]//cvxReduce,d["vars"]];
If[f["verbose"],Echo[StringForm["Support `` computed directly",sol],{f["name"],"Support"}]];
,
If[f["verbose"],Echo[StringForm["Support `` computed using stationarySupport",sol],{f["name"],"Support"}]];
];

,
sol=support[d["expr"]//cvxReduce,d["vars"]];
If[f["verbose"],Echo[StringForm["Support `` computed directly",sol],{f["name"],"Support"}]];
];

Echo[List[sol,Fold[And,Element[#,Reals]&/@d["vars"]]&&d["cnd"]]];
dObj=initializeFunction[{cvxResolveOverReals[sol,d["vars"],d["cnd"]],d["cnd"]},d["vars"],Name->\[Sigma][f["name"]]];
Echo[dObj["expr"],{f["name"],"Support"}];
If[True,AppendTo[dObj["data"],"supportOf"->f]];

dObj
]
optSet[ix_]["init","polar"]:=Module[{f=optSet[ix],d=optSet[ix]["data"],dObj,polarGauge,polarExpr},
polarGauge=f["support"];
polarExpr=FullSimplify[cvxResolveOverReals[polarGauge["expr"]<=1,d["vars"],d["cnd"]],d["cnd"]];

dObj=initializeSet[{polarExpr,d["cnd"]},f["vars"](*formalCovector[f["vars"]]*),Name->polar[f["name"]]];
If[!f["contains0"],
(*Echo[contains0polar];*)
polarGauge=initializeFunction[Max[polarGauge,0],f["vars"],Name->gauge[polar[f["name"]]]]
];

If[True,AppendTo[dObj["data"],"polarOf"->f]];

If[True,AppendTo[dObj["data"],"contains0"->True]];(* always true *)

If[True,AppendTo[polarGauge["data"],"lev"->dObj]];
If[True,AppendTo[dObj["data"],"gauge"->polarGauge]];
(*If[f["contains0"],AppendTo[dObj["data"],"bounded"->True]];*)(* this has to be stated for optSet[x^2-y-1<=1/.Thread[{x,y}->RotationMatrix[0].({x,y}-1/8)],{x,y}]["polar"], removed for epi graphs *)
If[isComputed[f,"polarOf"],AppendTo[dObj["data"],"zeroHull"->f["polarOf"]]];

If[f["contains0"],AppendTo[dObj["data"],"polar"->f]
];

dObj
]
optSet[ix_]["init","gauge"]:=Module[{f=optSet[ix],d=optSet[ix]["data"],dObj,polarGauge},
dObj=optSet[ix]["polar"]["support"];
If[True,AppendTo[dObj["data"],"lev"->f]];
dObj
]
optSet[ix_]["init","normalizedNormalCone"]:=Grad[optSet[ix]["gauge"]["expr"],optSet[ix]["vars"]]


(* ::Input:: *)
(*FunctionConvexity[Sqrt[a^2 x^2+b^2 y^2],{x,y},Reals]*)


(* ::Input:: *)
(*f=initializeSet[{{x/a,y/b} . {x/a,y/b}<=1,(a|b)\[Element]Reals&&(a|b)!=0},{x,y}]*)
(*f["polar"]["polar"]*)
(*g=objRelationGraph[f,TrivialEdges->False]*)


(* ::Input:: *)
(*MatchQ[1/2,1/_Integer]*)


(* ::Input:: *)
(*Simplify[x^2+y^2>=0,(x|y)\[Element]Reals]*)


(* ::Input:: *)
(*vars={x,y}*)
(*Power[x^2+y^2,1/2]<=1*)


(* ::Input:: *)
(*Reduce[x^2+y^2>=0,Reals]*)


(* ::Input:: *)
(*cnd=({x,y,z} . {x,y,z}<=1/.x->x-1/2)&&({x,y,z} . {x,y,z}<=1/.x->x+1/2)&&({x,y,z} . {x,y,z}<=1/.z->z+1/2)&&({x,y,z} . {x,y,z}<=1/.z->z-1/2)*)
(*vars={x,y,z}*)
(*F0=initializeSet[cnd,vars,Name->F]*)
(*F0["contains0"]*)


(* ::Input:: *)
(*.*)


(* ::Input:: *)
(*Module[{hlRules, f =F0},*)
(*  hlRules = # -> Style[#, FontColor -> Blue, FontWeight -> Medium] & /@ f["vars"];*)
(*  Tooltip[*)
(*   Panel[Magnify[f["expr"] /. hlRules // TraditionalForm, 1.25], *)
(*    FrameMargins -> 0],*)
(*   f["data"]]]*)


(* ::Input:: *)
(*F0["expr"]*)


(* ::Input::Initialization:: *)
formatMode="dynamic";
setOptFormat[formatMode_]:=Switch[formatMode,
"bare",(FormatValues[#]={})&/@{optFun,optMaxFun,optSet,optIntSet};,
"expr",
(*optInstance[_,_,ix_,h_]:=h[ix];*)
exprFormater[(f_optFun|f_optMaxFun|f_optSet|f_optIntSet)]:=optInstance[f["expr"],f["vars"],f[[1]],Head@f];
Format[optFun[id_]]:=exprFormater[optFun[id]];
Format[optMaxFun[id_]]:=exprFormater[optMaxFun[id]];
Format[optSet[id_]]:=exprFormater[optSet[id]];
Format[optIntSet[id_]]:=exprFormater[optIntSet[id]];,
"noButton",
formatExpr[optFun[id_]]:=Module[{hlRules,f=optFun[id]},
hlRules=#->Style[#,FontColor->Blue,FontWeight->Medium]&/@f["vars"];
Panel[Magnify[f["expr"]/.hlRules//TraditionalForm,1.25],FrameMargins->0,Background->Lighter[Gray,0.95]]
];
formatExpr[optSet[id_]]:=Module[{hlRules,f=optSet[id]},
hlRules=#->Style[#,FontColor->Blue,FontWeight->Medium]&/@f["vars"];
Panel[Magnify[f["expr"]/.hlRules//TraditionalForm,1.25],FrameMargins->0]
];
formatExpr[optMaxFun[id_]]:=Module[{f=optMaxFun[id],c=optMaxFun[id]["children"]},
Panel[CirclePlus@@Deploy/@c,FrameMargins->0]
];
formatExpr[optIntSet[id_]]:=Module[{f=optIntSet[id],c=optIntSet[id]["children"]},
Panel[And@@Deploy/@c,FrameMargins->0]
];
formatName[(f_optFun|f_optMaxFun)]:=Style[f["name"],FontColor->Blue,FontWeight->Medium];
formatName[(f_optSet|f_optIntSet)]:=Style[f["name"],FontColor->Purple,FontWeight->Medium];
(*(h_optFun|h_optMaxFun|h_optSet|h_optIntSet)*)
dynamicOptFormater[(f_optFun|f_optMaxFun|f_optSet|f_optIntSet)]:=Tooltip[formatExpr[f],{Head[f],f[[1]],f["name"]}];
Format[optFun[id_]]:=dynamicOptFormater[optFun[id]];
Format[optMaxFun[id_]]:=dynamicOptFormater[optMaxFun[id]];
Format[optSet[id_]]:=dynamicOptFormater[optSet[id]];
Format[optIntSet[id_]]:=dynamicOptFormater[optIntSet[id]];,
"dynamic",
formatExpr[optFun[id_]]:=Module[{hlRules,f=optFun[id]},
hlRules=#->Style[#,FontColor->Blue,FontWeight->Medium]&/@f["vars"];
Panel[Magnify[f["expr"]/.hlRules//TraditionalForm,1.25],FrameMargins->0,Background->Lighter[Gray,0.95]]
];
formatExpr[optSet[id_]]:=Module[{hlRules,f=optSet[id]},
hlRules=#->Style[#,FontColor->Blue,FontWeight->Medium]&/@f["vars"];
Panel[Magnify[f["expr"]/.hlRules//TraditionalForm,1.25],FrameMargins->0]
];
formatExpr[optMaxFun[id_]]:=Module[{f=optMaxFun[id],c=optMaxFun[id]["children"]},
Panel[CirclePlus@@Deploy/@c,FrameMargins->0]
];
formatExpr[optIntSet[id_]]:=Module[{f=optIntSet[id],c=optIntSet[id]["children"]},
Panel[And@@Deploy/@c,FrameMargins->0]
];
formatName[(f_optFun|f_optMaxFun)]:=Style[f["name"],FontColor->Blue,FontWeight->Medium];
formatName[(f_optSet|f_optIntSet)]:=Style[f["name"],FontColor->Purple,FontWeight->Medium];
(*(h_optFun|h_optMaxFun|h_optSet|h_optIntSet)*)
dynamicOptFormater[(f_optFun|f_optMaxFun|f_optSet|f_optIntSet)]:=DynamicModule[{showingPanel=False,usingNames=False,tabChoice=1},
Dynamic[Refresh[DynamicModule[{nameDisplay,selectorPanel},
nameDisplay=If[usingNames,formatName[f],formatExpr[f]];
selectorPanel=Tooltip[Toggler[Dynamic[showingPanel],#->nameDisplay&/@{True,False}],
{Head[f],f[[1]],f["name"]}];
Column[{
selectorPanel,
Sequence@@If[!showingPanel,{},{TabView[{
"DataSet"->Dataset[f["data"]],
"Plots"->Dynamic[Refresh[
If[tabChoice==2,
(* [Preset dropdown] [code textbox] [copy button] [evaluate button]*)
plot[f],
"Generating ..."]
,TrackedSymbols:>{tabChoice}]]
},Dynamic[tabChoice],FrameMargins->0]}]
}]
],TrackedSymbols:>{showingPanel}]]
];
Format[optFun[id_]]:=dynamicOptFormater[optFun[id]];
Format[optMaxFun[id_]]:=dynamicOptFormater[optMaxFun[id]];
Format[optSet[id_]]:=dynamicOptFormater[optSet[id]];
Format[optIntSet[id_]]:=dynamicOptFormater[optIntSet[id]];
]
setOptFormat["noButton"]


(* ::Subsection:: *)
(*unbounded*)


(* ::Input:: *)
(*setOptFormat["noButton"]*)
(*f=initializeFunction[Max[(x-1)^2,(x+1)^2],{x}]*)
(*f["epi"]["gauge"]*)
(*g=objRelationGraph[f,TrivialEdges->False]*)


(* ::Input:: *)
(*FullSimplify[Max[1/Sqrt[a/(x^2+y^2)],-(Sqrt[x^2+y^2]/Sqrt[a])],x\[Element]Reals&&y\[Element]Reals&&a>0]*)


(* ::Input:: *)
(*f["polar"]["data"]*)


(* ::Input:: *)
(*plot[f["polar"],3]*)


(* ::Input:: *)
(*Reduce[Alternatives[-x-Sqrt[2] Sqrt[x] Sqrt[y]-y,-x+Sqrt[2] Sqrt[x] Sqrt[y]-y]\[Element]Reals&&(x|y)\[Element]Reals,{x,y}]*)
(*RegionPlot[%,{x,-1,1},{y,-1,1}]*)


(* ::Input:: *)
(*Plot3D[List[-x-Sqrt[2] Sqrt[x] Sqrt[y]-y,-x+Sqrt[2] Sqrt[x] Sqrt[y]-y],{x,-3,3},{y,-3,3}]*)


(* ::Input:: *)
(*ContourPlot[-x+Sqrt[2] Sqrt[x] Sqrt[y]-y,{x,-3,3},{y,-3,3}]*)


(* ::Input:: *)
(**)


(* ::Input:: *)
(*cplot[f["polar"]["polar"]["gauge"],4]*)
(*plot[f["polar"]["polar"]](* we should actually be slicing a multi avlued function*)*)


(* ::Input:: *)
(*plot[f["polar"],5]*)


(* ::Input:: *)
(**)


(* ::Input:: *)
(*FunctionConvexity[-x-y+Sqrt[x^2+y^2],{x,y}]*)


(* ::Input:: *)
(*f["expr"]*)
(*f["support"]["expr"]*)
(*f["polar"]["expr"]*)


(* ::Subsection:: *)
(*Support Functions (Implicit)*)


(* ::Input::Initialization:: *)
simpleSupport[cons_LessEqual,vars_,cnds_:True]:=Module[{newVars=formalVector[vars],exprNew,sols,cvxCases},
(* assumes cons is convex, bounded, and contains 0 *)
exprNew=cons/.Thread[vars->newVars];
sols=FullSimplify@lagrangeStationaryPoints[vars . newVars,exprNew/.LessEqual->Equal,newVars];
cvxCases=Select[sols,FunctionConvexity[{#,cnds},vars]==1&];
If[Length[cvxCases]!=1,Echo[{sols,FunctionConvexity[{#,cnds},vars]&/@sols,cnds,vars,cvxCases},{simpleSupport,convexityIssue}];cvxCases=Max@sols];
Simplify[cvxCases[[1]],Element[Alternatives@@vars,Reals]]
]


(* ::Input:: *)
(*RepeatedTiming[support[{x,y} . {x,y}<=3,{x,y}],1]*)
(*RepeatedTiming[simpleSupport[{x,y} . {x,y}<=3,{x,y}],1]*)


(* ::Input:: *)
(*f=initializeSet[{ x, y} . { x,y}<=1/.Thread[{x,y}->{x,y}+1],{x,y}]*)
(*f["polar"]["polar"]*)
(*g=objRelationGraph[f,TrivialEdges->False]*)


(* ::Input:: *)
(*Manipulate[Show[{RegionPlot[Sqrt[{ x, y} . { x,y}]<=1,{x,-1,1},{y,-1,1}],RegionPlot[x^2+y^2<=1,{x,-1,1},{y,-1,1}]}],{a,0.5,1}]*)


(* ::Input:: *)
(*Manipulate[Show[{RegionPlot[Sqrt[{ x, y} . { x,y}/a]<=1,{x,-1,1},{y,-1,1}],RegionPlot[x^2+y^2<=a,{x,-1,1},{y,-1,1}]}],{a,0.5,1}]*)


(* ::Input:: *)
(*{ x, y} . { x,y}<=a//FullSimplify*)
(*Sqrt[{ x, y} . { x,y}/a]<=1//FullSimplify*)


(* ::Input:: *)
(*f=initializeSet[{x,y} . {x,y}<=1/.x->x-2,{x,y}]*)
(*f["polar"]["polar"]*)
(*g=objRelationGraph[f,TrivialEdges->False]*)


(* ::Input::Initialization:: *)
optSet[ix_]["init","boundaryAtlas"]:=Module[{obj=optSet[ix]},boundaryAtlas[obj["expr"],obj["vars"]]]


(* ::Input:: *)
(*RepeatedTiming[support[{x,y} . {x,y}<=3,{x,y}],1]*)
(*RepeatedTiming[simpleSupport[{x,y} . {x,y}<=3,{x,y}],1]*)


(* ::Input:: *)
(*f=initializeSet[{ x, y} . { x,y}<=1/.Thread[{x,y}->{x,y}+1],{x,y}]*)
(*f["polar"]["polar"]*)
(*g=objRelationGraph[f,TrivialEdges->False]*)


(* ::Input:: *)
(*Manipulate[Show[{RegionPlot[Sqrt[{ x, y} . { x,y}]<=1,{x,-1,1},{y,-1,1}],RegionPlot[x^2+y^2<=1,{x,-1,1},{y,-1,1}]}],{a,0.5,1}]*)


(* ::Input:: *)
(*Manipulate[Show[{RegionPlot[Sqrt[{ x, y} . { x,y}/a]<=1,{x,-1,1},{y,-1,1}],RegionPlot[x^2+y^2<=a,{x,-1,1},{y,-1,1}]}],{a,0.5,1}]*)


(* ::Input:: *)
(*{ x, y} . { x,y}<=a//FullSimplify*)
(*Sqrt[{ x, y} . { x,y}/a]<=1//FullSimplify*)


(* ::Input:: *)
(*f=initializeSet[{x,y} . {x,y}<=1/.x->x-2,{x,y}]*)
(*f["polar"]["polar"]*)
(*g=objRelationGraph[f,TrivialEdges->False]*)


(* ::Input::Initialization:: *)
optSet[ix_]["init","boundaryAtlas"]:=Module[{obj=optSet[ix]},boundaryAtlas[obj["expr"],obj["vars"]]]
