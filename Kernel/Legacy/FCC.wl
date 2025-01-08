(* ::Package:: *)

Package["ConvexAnalysisGeometry`Legacy`FCC"]


(* ::Subsection::Closed:: *)
(*dev_ind*)


(* ::Input::Initialization:: *)
Format[ind[fx_,x_,{a_,b_}],TraditionalForm]:=Subscript[\!\(\*SubscriptBox[\(\[Delta]\), \("\<[\>" <> ToString[a] <> "\<, \>" <> ToString[b] <> "\<]\>"\)]\)[fx], x]
Format[ind[x_,x_,{a_,b_}],TraditionalForm]:=\!\(\*SubscriptBox[\(\[Delta]\), \("\<[\>" <> ToString[a] <> "\<, \>" <> ToString[b] <> "\<]\>"\)]\)[x]


(* ::Input::Initialization:: *)
ind[\[Lambda]_ fz_+\[Delta]_,z_Symbol,{a_,b_}]/;
!FreeQ[fz,z]:=
ind[fz,z,{( a-\[Delta])/\[Lambda],( b-\[Delta])/\[Lambda]}]

ind[\[Lambda]_ fz_,z_Symbol,{a_,b_}]/;
!FreeQ[fz,z]:=
ind[fz,z,{a/\[Lambda], b/\[Lambda]}]

ind[fz_+\[Delta]_,z_Symbol,{a_,b_}]/;
!FreeQ[fz,z]:=
ind[fz,z,{ a-\[Delta], b-\[Delta]}]


(* ::Input::Initialization:: *)
ind[g_[fz_],z_Symbol,{a_,b_}]/;
!FreeQ[fz,z]&&
(FunctionInjective[g[fz],z,PerformanceGoal->"Speed"]
||FunctionInjective[{g[fz],a<z<b},z,PerformanceGoal->"Speed"]):=
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


(* ::Input::Initialization:: *)
ind[fz_,z_Symbol,False]:=\[Infinity]


(* ::Input::Initialization:: *)
ind[x,x,R_EmptyRegion]:=\[Infinity]


(* ::Input::Initialization:: *)
ind[z_,z_,ImplicitRegion[a_<fz_,{z_}]]/;
!FreeQ[fz,z]&&FreeQ[a,z]:=
ind[fz,z,{a,\[Infinity]}]
ind[z_,z_,ImplicitRegion[fz_<b_,{z_}]]/;
!FreeQ[fz,z]&&FreeQ[b,z]:=
ind[fz,z,{-\[Infinity],b}]
ind[z_,z_,ImplicitRegion[a_<fz_<b_,{z_}]]/;
!FreeQ[fz,z]&&FreeQ[{a,b},z]:=
ind[fz,z,{a,b}]

ind[gz_,z_,ImplicitRegion[fz_,{z_}]]/;
!SameQ[z,gz]&&!FreeQ[{fz,gz},z]:=
ind[z,z,ImplicitRegion[fz/.z->gz,{z}]]


(* ::Subsubsection::Closed:: *)
(*Infimal Convolution*)


(* ::Input::Initialization:: *)
infconv[fx_,ind[x_,x_,indBnds_],x_]/;
!FreeQ[fx,x]:=
Module[{f=Evaluate[fx/.x->#]&,minX},
(*TODO: add tests for certain simplified forms, using sign and abs *)
minX=SolveValues[D[f[x],x]==0,{x},Reals,Cubics->True,Quartics->True][[1,1]];
\!\(\*
TagBox[GridBox[{
{"\[Piecewise]", GridBox[{
{
RowBox[{"f", "[", 
RowBox[{"x", "+", "minX", "-", 
RowBox[{"indBnds", "[", 
RowBox[{"[", "1", "]"}], "]"}]}], "]"}], 
RowBox[{"x", "<=", 
RowBox[{"indBnds", "[", 
RowBox[{"[", "1", "]"}], "]"}]}]},
{
RowBox[{"f", "[", "minX", "]"}], 
RowBox[{
RowBox[{"indBnds", "[", 
RowBox[{"[", "1", "]"}], "]"}], "<", "x", "<=", 
RowBox[{"indBnds", "[", 
RowBox[{"[", "2", "]"}], "]"}]}]},
{
RowBox[{"f", "[", 
RowBox[{"x", "+", "minX", "-", 
RowBox[{"indBnds", "[", 
RowBox[{"[", "2", "]"}], "]"}]}], "]"}], "True"}
},
AllowedDimensions->{2, Automatic},
Editable->True,
GridBoxAlignment->{"Columns" -> {{Left}}, "ColumnsIndexed" -> {}, "Rows" -> {{Baseline}}, "RowsIndexed" -> {}},
GridBoxItemSize->{"Columns" -> {{Automatic}}, "ColumnsIndexed" -> {}, "Rows" -> {{1.}}, "RowsIndexed" -> {}},
GridBoxSpacings->{"Columns" -> {Offset[0.27999999999999997`], {Offset[0.84]}, Offset[0.27999999999999997`]}, "ColumnsIndexed" -> {}, "Rows" -> {Offset[0.2], {Offset[0.4]}, Offset[0.2]}, "RowsIndexed" -> {}},
Selectable->True]}
},
GridBoxAlignment->{"Columns" -> {{Left}}, "ColumnsIndexed" -> {}, "Rows" -> {{Baseline}}, "RowsIndexed" -> {}},
GridBoxItemSize->{"Columns" -> {{Automatic}}, "ColumnsIndexed" -> {}, "Rows" -> {{1.}}, "RowsIndexed" -> {}},
GridBoxSpacings->{"Columns" -> {Offset[0.27999999999999997`], {Offset[0.35]}, Offset[0.27999999999999997`]}, "ColumnsIndexed" -> {}, "Rows" -> {Offset[0.2], {Offset[0.4]}, Offset[0.2]}, "RowsIndexed" -> {}}],
"Piecewise",
DeleteWithContents->True,
Editable->False,
SelectWithContents->True,
Selectable->False,
StripWrapperBoxes->True]\)
]


(* ::Subsection::Closed:: *)
(*dev_pwl*)


(* ::Input::Initialization:: *)
pwlSlopes[pwl[l_List]]:=#2/#1&@@Transpose@Differences[l]
convexQ[f_pwl]:=OrderedQ@pwlSlopes[f]
pwl2fun[pwl[l_List]]:=Module[{sl,xVals,xBnds,cnds,crnrPts,linFuns,pwPairs,pwFun,x},
sl=pwlSlopes[pwl[l]];
xVals=l[[;;,1]];
(* note the first and last entries are not corner points *)
xBnds=Partition[Join[{-Infinity},xVals[[2;;-2]],{Infinity}],2,1];
cnds=#1<=x<#2&@@@xBnds;
crnrPts=Prepend[l[[2;;-2]],l[[2]]];
linFuns=(x-crnrPts[[;;,1]])*sl+crnrPts[[;;,2]];
pwPairs=Transpose[{linFuns,cnds}];
(* working with standard Piecewise spec *)
pwFun=Piecewise[pwPairs[[;;-2]],pwPairs[[-1,1]]];
Evaluate[pwFun/.x->#]&
]


(* ::Subsubsection::Closed:: *)
(*sg*)


(* ::Input::Initialization:: *)
sg[fpwl_pwl]:=Module[
{slps=pwlSlopes[fpwl],l=fpwl[[1]],
innerPairs},
innerPairs=(Sequence@@(Prepend[#1]/@List/@#2)&)@@@Transpose[{l[[2;;-2,1]],Partition[slps,2,1]}];
pwl[{{l[[1,1]],slps[[1]]},Sequence@@innerPairs,{l[[-1,1]],slps[[-1]]}}]
]


(* ::Subsubsection::Closed:: *)
(*infconv*)


(* ::Input::Initialization:: *)
infconv[fx_,pwl[l_List],x_]/;
Length[l]==3&&convexQ[pwl[l]]:=
Module[{fpwl=pwl[l],f=Evaluate[fx/.x->#]&,
fpwlFun,slps,xc,yc,df,x1,x0},
fpwlFun=pwlToFun@fpwl;
slps=pwlSlopes[fpwl];
{xc,yc}=fpwl[[1]][[2]];
(* (convex, differentiable, -> Infinity on both sides?) with (2-part cvx pwl). TODO: make the solve work for subgradients *)
df=D[f[x],x];
x1=SolveValues[df==slps[[2]],{x},Reals,Cubics->True,Quartics->True][[1,1]];
x0=SolveValues[df==slps[[1]],{x},Reals,Cubics->True,Quartics->True][[1,1]];
\!\(\*
TagBox[GridBox[{
{"\[Piecewise]", GridBox[{
{
RowBox[{
RowBox[{
RowBox[{"slps", "[", 
RowBox[{"[", "1", "]"}], "]"}], 
RowBox[{"(", 
RowBox[{"x", "-", "xc", "-", "x0"}], ")"}]}], "+", 
RowBox[{"f", "[", "x0", "]"}], "+", "yc"}], 
RowBox[{
RowBox[{"x", "-", "xc"}], "<=", "x0"}]},
{
RowBox[{
RowBox[{"f", "[", 
RowBox[{"x", "-", "xc"}], "]"}], "+", "yc"}], 
RowBox[{"x0", "<", 
RowBox[{"x", "-", "xc"}], "<", "x1"}]},
{
RowBox[{
RowBox[{
RowBox[{"slps", "[", 
RowBox[{"[", "2", "]"}], "]"}], 
RowBox[{"(", 
RowBox[{"x", "-", "xc", "-", "x1"}], ")"}]}], "+", 
RowBox[{"f", "[", "x1", "]"}], "+", "yc"}], "True"}
},
AllowedDimensions->{2, Automatic},
Editable->True,
GridBoxAlignment->{"Columns" -> {{Left}}, "ColumnsIndexed" -> {}, "Rows" -> {{Baseline}}, "RowsIndexed" -> {}},
GridBoxItemSize->{"Columns" -> {{Automatic}}, "ColumnsIndexed" -> {}, "Rows" -> {{1.}}, "RowsIndexed" -> {}},
GridBoxSpacings->{"Columns" -> {Offset[0.27999999999999997`], {Offset[0.84]}, Offset[0.27999999999999997`]}, "ColumnsIndexed" -> {}, "Rows" -> {Offset[0.2], {Offset[0.4]}, Offset[0.2]}, "RowsIndexed" -> {}},
Selectable->True]}
},
GridBoxAlignment->{"Columns" -> {{Left}}, "ColumnsIndexed" -> {}, "Rows" -> {{Baseline}}, "RowsIndexed" -> {}},
GridBoxItemSize->{"Columns" -> {{Automatic}}, "ColumnsIndexed" -> {}, "Rows" -> {{1.}}, "RowsIndexed" -> {}},
GridBoxSpacings->{"Columns" -> {Offset[0.27999999999999997`], {Offset[0.35]}, Offset[0.27999999999999997`]}, "ColumnsIndexed" -> {}, "Rows" -> {Offset[0.2], {Offset[0.4]}, Offset[0.2]}, "RowsIndexed" -> {}}],
"Piecewise",
DeleteWithContents->True,
Editable->False,
SelectWithContents->True,
Selectable->False,
StripWrapperBoxes->True]\)
]
infconv[fx_,Abs[x_],x_]:=infconv[fx,pwl[{{-1,1},{0,0},{1,1}}],x]


(* ::Subsubsection::Closed:: *)
(*slfc*)


(* ::Input::Initialization:: *)
(* a point on the line segment with slope s_i will maximize (s_i x - f[x]) = s_i x_i - y_i *)
slfc[pwl[l_List],x_Symbol]/;convexQ[pwl[l]]:=pwl[Transpose[{#,#*l[[2;;,1]]-l[[2;;,2]]}]]+ind[z,z,MinMax[#]]&[pwlSlopes[pwl[l]]]


(* ::Subsubsection::Closed:: *)
(*Max Form {normal_List,level_Symbol}*)


(* ::Input::Initialization:: *)
colThread[f_[x_List, y_List]] := Thread[f[Flatten@x, Flatten@y]]


(* ::Input::Initialization:: *)
(*pwl2Fun[pwl["max",A_,b_]]/;MatrixQ[A]&&MatrixQ[b]:=Module[{XX=Array[Subscript[x, #2]&,{1,Dimensions[A,2][[2]]}]},
Max@@colThread[A.XX==b]]*)
pwl2Fun0[pwl["max",A_,b_]]/;MatrixQ[A]&&MatrixQ[b]:=Module[{m},(Max@@colThread[m[A . Transpose[{##}],b]])/.m[u_,v_]:>u-v]&

pwl2Fun[pwl["max",A_,b_]]/;MatrixQ[A]&&MatrixQ[b]:=Module[{x,XX,m},
XX=Array[Subscript[x, #1]&,{Dimensions[A,2][[2]],1}];
(Max@@colThread[m[A . XX,b]])/.m[u_,v_]:>u-v]


(* ::Input::Initialization:: *)
(* conversions to normal form - must go last? *)
pwl["max",A_,b_]/;!MatrixQ[A]:=pwl["max",Transpose[{A}],b]
pwl["max",A_,b_]/;!MatrixQ[b]:=pwl["max",A,Transpose[{b}]]


(* ::Subsection::Closed:: *)
(*dev_slfc_v2*)


(* ::Input::Initialization:: *)
Format[slfc[f_[fx_],x_],TraditionalForm]:=Subscript[SuperStar[f][fx], x]
Format[slfc[x_],TraditionalForm]:=SuperStar[x]
Format[subs[slfc[f_[fx_],x_],slfc[x_]->expr_],TraditionalForm]:=Subscript[SuperStar[f][fx], x][expr]


(* ::Input::Initialization:: *)
wlEval[slfc[fx_,x_]]:=Module[{z},MaxValue[z*x-(fx/.x->z),x]/.z->slfc[x]]


(* ::Input::Initialization:: *)
subs[exp_slfc,rule_]:=Hold[subs[exp,rule]](* not sure? *)


(* ::Text:: *)
(*Additive Combinations*)


(* ::Input::Initialization:: *)
slfc[L1_+L2_,{x_,v_}]/;
FreeQ[L1,v]&&FreeQ[L2,x]:=
slfc[L1,x]+slfc[L2,v]


(* ::Text:: *)
(*Scaling properties*)


(* ::Input:: *)
(*slfc[a2_.+fx_.*mx_.+m2_.*f_[a1_.+fx_.*m1_.],x_]/;!FreeQ[fx,x]&&FreeQ[{a1,a2,f,m1,m2,mx},x]&&m2>0:=-a2-(a1*(-mx+slfc[x])/m1)+m2*subs[slfc[f[fx],x],slfc[x]->(-mx+slfc[x])/(m1*m2)];*)


(* ::Input::Initialization:: *)
(* TODO: Context Tracking, ensure convexity of f (+make it recognize things like x^2k)*)
slfc[a2_+fx_*mx_+m2_*f_[a1_+fx_*m1_],x_]/;
convexQ[f]&&!FreeQ[fx,x]&&FreeQ[{a1,a2,f,m1,m2,mx},x]&&m2>0:=
-a2-(a1*(-mx+slfc[x]))/m1+m2*subs[slfc[f[fx],x],slfc[x]->(-mx+slfc[x])/(m1*m2)];

(* all combinations programatically generated *)
slfc[a2_+fx_*mx_+m2_*f_[fx_*m1_],x_]/;convexQ[f]&&!FreeQ[fx,x]&&FreeQ[{a2,f,m1,m2,mx},x]&&m2>0:=-a2+m2*subs[slfc[f[fx],x],slfc[x]->(-mx+slfc[x])/(m1*m2)];
slfc[fx_*mx_+m2_*f_[a1_+fx_*m1_],x_]/;convexQ[f]&&!FreeQ[fx,x]&&FreeQ[{a1,f,m1,m2,mx},x]&&m2>0:=-((a1*(-mx+slfc[x]))/m1)+m2*subs[slfc[f[fx],x],slfc[x]->(-mx+slfc[x])/(m1*m2)];
slfc[a2_+m2_*f_[a1_+fx_*m1_],x_]/;convexQ[f]&&!FreeQ[fx,x]&&FreeQ[{a1,a2,f,m1,m2},x]&&m2>0:=-a2-(a1*slfc[x])/m1+m2*subs[slfc[f[fx],x],slfc[x]->slfc[x]/(m1*m2)];
slfc[a2_+fx_*mx_+m2_*f_[a1_+fx_],x_]/;convexQ[f]&&!FreeQ[fx,x]&&FreeQ[{a1,a2,f,m2,mx},x]&&m2>0:=-a2-a1*(-mx+slfc[x])+m2*subs[slfc[f[fx],x],slfc[x]->(-mx+slfc[x])/m2];
slfc[a2_+fx_*mx_+f_[a1_+fx_*m1_],x_]/;convexQ[f]&&!FreeQ[fx,x]&&FreeQ[{a1,a2,f,m1,mx},x]:=-a2-(a1*(-mx+slfc[x]))/m1+subs[slfc[f[fx],x],slfc[x]->(-mx+slfc[x])/m1];
slfc[fx_*mx_+m2_*f_[fx_*m1_],x_]/;convexQ[f]&&!FreeQ[fx,x]&&FreeQ[{f,m1,m2,mx},x]&&m2>0:=m2*subs[slfc[f[fx],x],slfc[x]->(-mx+slfc[x])/(m1*m2)];
slfc[a2_+m2_*f_[fx_*m1_],x_]/;convexQ[f]&&!FreeQ[fx,x]&&FreeQ[{a2,f,m1,m2},x]&&m2>0:=-a2+m2*subs[slfc[f[fx],x],slfc[x]->slfc[x]/(m1*m2)];
slfc[a2_+fx_*mx_+m2_*f_[fx_],x_]/;convexQ[f]&&!FreeQ[fx,x]&&FreeQ[{a2,f,m2,mx},x]&&m2>0:=-a2+m2*subs[slfc[f[fx],x],slfc[x]->(-mx+slfc[x])/m2];
slfc[a2_+fx_*mx_+f_[fx_*m1_],x_]/;convexQ[f]&&!FreeQ[fx,x]&&FreeQ[{a2,f,m1,mx},x]:=-a2+subs[slfc[f[fx],x],slfc[x]->(-mx+slfc[x])/m1];
slfc[m2_*f_[a1_+fx_*m1_],x_]/;convexQ[f]&&!FreeQ[fx,x]&&FreeQ[{a1,f,m1,m2},x]&&m2>0:=-((a1*slfc[x])/m1)+m2*subs[slfc[f[fx],x],slfc[x]->slfc[x]/(m1*m2)];
slfc[fx_*mx_+m2_*f_[a1_+fx_],x_]/;convexQ[f]&&!FreeQ[fx,x]&&FreeQ[{a1,f,m2,mx},x]&&m2>0:=-(a1*(-mx+slfc[x]))+m2*subs[slfc[f[fx],x],slfc[x]->(-mx+slfc[x])/m2];
slfc[fx_*mx_+f_[a1_+fx_*m1_],x_]/;convexQ[f]&&!FreeQ[fx,x]&&FreeQ[{a1,f,m1,mx},x]:=-((a1*(-mx+slfc[x]))/m1)+subs[slfc[f[fx],x],slfc[x]->(-mx+slfc[x])/m1];
slfc[a2_+m2_*f_[a1_+fx_],x_]/;convexQ[f]&&!FreeQ[fx,x]&&FreeQ[{a1,a2,f,m2},x]&&m2>0:=-a2-a1*slfc[x]+m2*subs[slfc[f[fx],x],slfc[x]->slfc[x]/m2];
slfc[a2_+f_[a1_+fx_*m1_],x_]/;convexQ[f]&&!FreeQ[fx,x]&&FreeQ[{a1,a2,f,m1},x]:=-a2-(a1*slfc[x])/m1+subs[slfc[f[fx],x],slfc[x]->slfc[x]/m1];
slfc[a2_+fx_*mx_+f_[a1_+fx_],x_]/;convexQ[f]&&!FreeQ[fx,x]&&FreeQ[{a1,a2,f,mx},x]:=-a2-a1*(-mx+slfc[x])+subs[slfc[f[fx],x],slfc[x]->-mx+slfc[x]];
slfc[m2_*f_[fx_*m1_],x_]/;convexQ[f]&&!FreeQ[fx,x]&&FreeQ[{f,m1,m2},x]&&m2>0:=m2*subs[slfc[f[fx],x],slfc[x]->slfc[x]/(m1*m2)];
slfc[fx_*mx_+m2_*f_[fx_],x_]/;convexQ[f]&&!FreeQ[fx,x]&&FreeQ[{f,m2,mx},x]&&m2>0:=m2*subs[slfc[f[fx],x],slfc[x]->(-mx+slfc[x])/m2];
slfc[fx_*mx_+f_[fx_*m1_],x_]/;convexQ[f]&&!FreeQ[fx,x]&&FreeQ[{f,m1,mx},x]:=subs[slfc[f[fx],x],slfc[x]->(-mx+slfc[x])/m1];
slfc[a2_+m2_*f_[fx_],x_]/;convexQ[f]&&!FreeQ[fx,x]&&FreeQ[{a2,f,m2},x]&&m2>0:=-a2+m2*subs[slfc[f[fx],x],slfc[x]->slfc[x]/m2];
slfc[a2_+f_[fx_*m1_],x_]/;convexQ[f]&&!FreeQ[fx,x]&&FreeQ[{a2,f,m1},x]:=-a2+subs[slfc[f[fx],x],slfc[x]->slfc[x]/m1];
slfc[a2_+fx_*mx_+f_[fx_],x_]/;convexQ[f]&&!FreeQ[fx,x]&&FreeQ[{a2,f,mx},x]:=-a2+subs[slfc[f[fx],x],slfc[x]->-mx+slfc[x]];
slfc[m2_*f_[a1_+fx_],x_]/;convexQ[f]&&!FreeQ[fx,x]&&FreeQ[{a1,f,m2},x]&&m2>0:=-(a1*slfc[x])+m2*subs[slfc[f[fx],x],slfc[x]->slfc[x]/m2];
slfc[f_[a1_+fx_*m1_],x_]/;convexQ[f]&&!FreeQ[fx,x]&&FreeQ[{a1,f,m1},x]:=-((a1*slfc[x])/m1)+subs[slfc[f[fx],x],slfc[x]->slfc[x]/m1];
slfc[fx_*mx_+f_[a1_+fx_],x_]/;convexQ[f]&&!FreeQ[fx,x]&&FreeQ[{a1,f,mx},x]:=-(a1*(-mx+slfc[x]))+subs[slfc[f[fx],x],slfc[x]->-mx+slfc[x]];
slfc[a2_+f_[a1_+fx_],x_]/;convexQ[f]&&!FreeQ[fx,x]&&FreeQ[{a1,a2,f},x]:=-a2-a1*slfc[x]+slfc[f[fx],x];
slfc[m2_*f_[fx_],x_]/;convexQ[f]&&!FreeQ[fx,x]&&FreeQ[{f,m2},x]&&m2>0:=m2*subs[slfc[f[fx],x],slfc[x]->slfc[x]/m2];
slfc[f_[fx_*m1_],x_]/;convexQ[f]&&!FreeQ[fx,x]&&FreeQ[{f,m1},x]:=subs[slfc[f[fx],x],slfc[x]->slfc[x]/m1];
slfc[fx_*mx_+f_[fx_],x_]/;convexQ[f]&&!FreeQ[fx,x]&&FreeQ[{f,mx},x]:=subs[slfc[f[fx],x],slfc[x]->-mx+slfc[x]];
slfc[a2_+f_[fx_],x_]/;convexQ[f]&&!FreeQ[fx,x]&&FreeQ[{a2,f},x]:=-a2+slfc[f[fx],x];
slfc[f_[a1_+fx_],x_]/;convexQ[f]&&!FreeQ[fx,x]&&FreeQ[{a1,f},x]:=-(a1*slfc[x])+slfc[f[fx],x];


(* ::Input::Initialization:: *)
slt[f_]:=Module[{x,y,sol,expr,pwList,x0},
sol=SolveValues[f'[x]==y,x,Reals];
x0=If[Length[sol]==1,
First[sol],
(* assume all conditional expressions *)
Assert[And@@(Head[#]===ConditionalExpression&/@sol),"assumed all conditional expressions were returned by solve"];
pwList=sol/.ConditionalExpression->List;
Piecewise[pwList[[1;;-2]],pwList[[-1,1]]]
];
expr=y x0-f[x0];
Evaluate[expr/.y->#]&]

(*
slt[f_]:=Module[{x,y,sol,expr,isCnd,cndFinite,pwList,x0},
sol=SolveValues[f'[x]==y,x,Reals];
isCnd=Head[#]===ConditionalExpression&/@sol;
{x0,cndFinite}=If[Length[sol]==1,
If[isCnd[[1]],
pwList=sol/.ConditionalExpression->List;
{pwList[[1,1]],pwList[[1,2]]},
{First[sol],False}
],
(* assume all conditional expressions *)
Assert[And@@isCnd,"assumed all conditional expressions were returned by solve"];
pwList=sol/.ConditionalExpression->List;
{
Piecewise[pwList[[1;;-2]],pwList[[-1,1]]],
Or@@Flatten[pwList[[;;,2]]]
}
];
expr=y x0-f[x0]+ind[y,y,cndFinite];
Evaluate[expr/.y->#]&]
(*Would need to: make ind work with conditions*)
*)

slfc[fx_,x_]/;
!FreeQ[fx,x]&&
FunctionConvexity[{fx,$Assumptions},x]>=0&&FunctionContinuous[{D[fx,x],$Assumptions},x,Reals]:=
slt[Evaluate[(fx/.x->#)&]][slfc[x]](*TODO add unique subgrad check*)
slfc[fx_,x_]/;
!FreeQ[fx,x]&&
FunctionConvexity[fx,x]>=0&&FunctionContinuous[D[fx,x],x,Reals]:=
slt[Evaluate[(fx/.x->#)&]][slfc[x]](*TODO figure out whats happening*)


(* ::Input::Initialization:: *)
slfc[Abs[x_],x_]:=ind[slfc[x],slfc[x],{-1,1}]
slfc[ind[x_,x_,{-1,1}],x_]:=Abs[slfc[x]]
slfc[ind[x_,x_,{m0_,m1_}],x_]:=\!\(\*
TagBox[GridBox[{
{"\[Piecewise]", GridBox[{
{
RowBox[{
FractionBox["1", "2"], 
RowBox[{"(", 
RowBox[{
RowBox[{
RowBox[{"-", "3"}], " ", "m0"}], "+", "m1"}], ")"}], " ", 
RowBox[{"slfc", "[", "x", "]"}]}], 
RowBox[{
RowBox[{"slfc", "[", "x", "]"}], ">", "0"}]},
{
RowBox[{
FractionBox["1", "2"], 
RowBox[{"(", 
RowBox[{
RowBox[{"3", "m0"}], "-", "m1"}], ")"}], " ", 
RowBox[{"slfc", "[", "x", "]"}]}], 
TagBox["True",
"PiecewiseDefault",
AutoDelete->True]}
},
AllowedDimensions->{2, Automatic},
Editable->True,
GridBoxAlignment->{"Columns" -> {{Left}}, "Rows" -> {{Baseline}}},
GridBoxItemSize->{"Columns" -> {{Automatic}}, "Rows" -> {{1.}}},
GridBoxSpacings->{"Columns" -> {Offset[0.27999999999999997`], {Offset[0.84]}, Offset[0.27999999999999997`]}, "Rows" -> {Offset[0.2], {Offset[0.4]}, Offset[0.2]}},
Selectable->True]}
},
GridBoxAlignment->{"Columns" -> {{Left}}, "Rows" -> {{Baseline}}},
GridBoxItemSize->{"Columns" -> {{Automatic}}, "Rows" -> {{1.}}},
GridBoxSpacings->{"Columns" -> {Offset[0.27999999999999997`], {Offset[0.35]}, Offset[0.27999999999999997`]}, "Rows" -> {Offset[0.2], {Offset[0.4]}, Offset[0.2]}}],
"Piecewise",
DeleteWithContents->True,
Editable->False,
SelectWithContents->True,
Selectable->False,
StripWrapperBoxes->True]\)


(* ::Input::Initialization:: *)
slfc[fx_+Abs[x_],x_]/;
!FreeQ[fx,x]:=infconv[slfc[fx,x],ind[slfc[x],slfc[x],{-1,1}],z]
(*TODO: check that slfc evaluates on left*)


(* ::Input::Initialization:: *)
slfc[fx_+ind[x_,x_,{m0_,m1_}],x_]/;
!FreeQ[fx,x]:=infconv[slfc[fx,x],pwl[{{-1,-(3m0-m1)/2},{0,0},{1,(m1-3 m0)/2}}],slfc[x]]
(*TODO: check that slfc evaluates on left*)
(*TODO: test m0 < m1 ... would not reduce symbolically *)
