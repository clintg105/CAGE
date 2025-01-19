#!/usr/bin/env wolframscript
(* ::Package:: *)

(* ::Section:: *)
(*RuleCanonicalDNFExpansion*)


(* ::Input::Initialization:: *)
Clear[
$RuleGreaterInnequalities,$RuleReduceRationals,
RuleCanonicalDNFExpansion
]

$RuleGreaterInnequalities={
x_<y_:>y>x,x_<=y_:>y>=x
};
$RuleReduceRationals={
(* moving implicit assumptions out of roots helps reduce *)
(* NOTE: makes all RHS zero *)
GreaterEqual[a_,c_]
/;c=!=0
:>GreaterEqual[Expand[Numerator[a]Denominator[c]-Numerator[c]Denominator[a]],0]&&Denominator[c]!=0&&Denominator[a]!=0,
Greater[a_,c_]
/;c=!=0
:>Greater[Expand[Numerator[a]Denominator[c]-Numerator[c]Denominator[a]],0]&&Denominator[c]!=0&&Denominator[a]!=0,
Equal[a_,c_]
/;c=!=0
:>Equal[Expand[Numerator[a]Denominator[c]-Numerator[c]Denominator[a]],0]&&Denominator[c]!=0&&Denominator[a]!=0
};

RuleCanonicalDNFExpansion[expr_]:=Module[{f,g,h},Block[{Plus},
SetAttributes[Plus,Orderless];
(*SetAttributes[h[0],Orderless];*)
SetAttributes[f,Orderless];
SetAttributes[g,Orderless];
((LogicalExpand/@BooleanMinimize[expr,"DNF"])
/.$RuleGreaterInnequalities/.{
Or->f,And->g,
a_==b_:>h[0][a,b],a_>=b_:>h[1][a,b],a_>b_:>h[2][a,b]
}//.{
(* De-Reduce innequalities *)
f[u___,
g[h[2][b_,a_],t___],
g[h[2][a_,b_],y___]
]/;g[t]===g[y]
:>f[g[a!=b,t],u],

(* De-Reduce quadratics *)
h[0][d_+b_. Sqrt[c_],a_]:>h[0][b Sqrt[c],a-d],
h[0][a_,d_+b_. Sqrt[c_]]:>h[0][a-d,b Sqrt[c]],
h[i_][a_,d_+b_. Sqrt[c_]]:>h[i][a-d,b Sqrt[c]],
h[i_][d_+b_. Sqrt[c_],a_]:>h[i][b Sqrt[c],a-d],

f[u___,
g[h[i_][a_,b_. Sqrt[c_]],t___],
g[h[i_][d_. Sqrt[c_],a_],y___]
]
/;b==-d&&g[t]===g[y]
:>f[g[h[i][b^2 c,a^2],t],u],
f[u___,
g[h[0][a_,b_. Sqrt[c_]],t___],
g[h[0][a_,d_. Sqrt[c_]],y___]
]
/;b==-d&&g[t]===g[y]
:>f[g[h[0][b^2 c,a^2],t],u],

g[y___,
h[i_][a_,b_. Sqrt[c_]],
h[i_][d_. Sqrt[c_],a_]
]
/;b==-d
:>g[h[i][b^2 c,a^2],y],

(* TODO: verify next block *)
f[u___,
g[h[i_?Positive][a_,b_. Sqrt[c_]],h[2][0,a],t___],
g[h[i_?Positive][d_. Sqrt[c_],a_],h[2][a,0],y___]]
/;b==-d&&g[t]===g[y]
:>f[g[h[i][a^2,b^2 c],t],u],
(*g[y___,
h[a_,b_. Sqrt[c_],i_?Positive],
h[d_. Sqrt[c_],a_,i_?Positive],
(h[0,a,2],h[a,0,2]|a!=0)]
/;b==-d
:>g[h[b^2 c,a^2,i],y],*)

f[u___,
g[h[0][b_. Sqrt[c_],a_],t___],
g[h[0][d_. Sqrt[c_],a_],y___]]
/;b==-d&&g[t]===g[y]
:>f[g[h[0][a^2,b^2 c],t],u]

(*,f[u___,
g[p_,t___],
g[q_,y___]
]
/;q==!p&&g[t]===g[y]
:>f[g[t,y],u]*)
}
)/.{f->Or,g->And,h[0][a_,b_]:>a==b,h[1][a_,b_]:>a>=b,h[2][a_,b_]:>a>b}
]]


(* ::Input:: *)
(*""*)


(* ::Input:: *)
(*exprRed0=# . #<=1&@{(x-1)/2,(y-3)/a}*)
(*exprLarge=Reduce[exprRed0]*)
(*LogicalExpand/@BooleanMinimize[exprLarge,"DNF"]*)
(*RuleCanonicalDNFExpansion[exprLarge]*)


(* ::Input:: *)
(*exprRed0=# . #>=1&@{(x-1)/2,(y-3)/a}*)
(*exprLarge=Reduce[exprRed0]*)
(*RuleCanonicalDNFExpansion[exprLarge]*)


(* ::Input:: *)
(*x-d//FullForm*)


(* ::Input:: *)
(*exprRed0=# . #<=1&@{(x-1/2)/2,(y-3)/a,(z-4/3)/8}*)
(*exprLarge=Reduce[exprRed0,Reals];*)
(*RuleCanonicalDNFExpansion[exprLarge]*)
(*%//.$RuleReduceRationals//FullSimplify*)


(* ::Input:: *)
(*(* this one was strangely tricky *)*)
(*exprRed0=# . #<=1&@{(x-1)/2,(y-3)/a,z-1/2,w}*)
(*exprLarge=Reduce[exprRed0,Reals];*)
(*RuleCanonicalDNFExpansion[exprLarge]*)
(*%//.$RuleReduceRationals//FullSimplify*)


(* ::Section:: *)
(*CanonicalizeSingleCandidateSearch*)


(* ::Input::Initialization:: *)
Clear[CanonicalizeSingleCandidateSearch]

CanonicalizeSingleCandidateSearch[expr_,varsAndParams_,assum_:True]:=Module[{
exprNoFrac=RuleCanonicalDNFExpansion[expr]
//.$RuleReduceRationals,
allSubExpr,candidateScores,feasibleCandidatePos,candidateScoreOrder,feasibleCandidates,bestCandidate
},
(* Look inside all And's & Or's in a logical expression and see if a single sub expression is equivalent to the whole thing under assum *)
allSubExpr=DeleteDuplicates@Flatten[exprNoFrac/.{Or->List,And->List}];
candidateScores=CountDistinct[Cases[#,Alternatives@@varsAndParams,Infinity]]&/@allSubExpr;
feasibleCandidatePos=Flatten@Position[candidateScores,x_/;x==Length@varsAndParams,1];
(* TODO: something with leaftcount and maybe OrderingBy *);
candidateScoreOrder=Ordering[-candidateScores[[feasibleCandidatePos]]];
feasibleCandidates=allSubExpr[[feasibleCandidatePos[[candidateScoreOrder]]]];
bestCandidate=SelectFirst[
feasibleCandidates,
SimplifyAssuming[
(* this Reduce typically requires fractions to be removed: `exprNoFrac` *)
Reduce[
Equivalent[#,exprNoFrac],
Reals],
assum]===True&
];
If[bestCandidate===Missing["NotFound"],expr,bestCandidate]
]


(* ::Input:: *)
(*exprRed0=# . #>=1&@{(x-1)/2,(y-3)/a}*)
(*exprLarge=Reduce[exprRed0]*)
(*RuleCanonicalDNFExpansion[exprLarge]//.$RuleReduceRationals*)
(*CanonicalizeSingleCandidateSearch[exprLarge,{x,y,a}]*)
(*CanonicalizeSingleCandidateSearch[exprLarge,{x,y,a},a!=0]*)


(* ::Input:: *)
(*exprRed0=# . #==1&@{(x-1)/2,(y-3)/a}*)
(*exprLarge=Reduce[exprRed0]*)
(*RuleCanonicalDNFExpansion[exprLarge]//.$RuleReduceRationals*)
(*CanonicalizeSingleCandidateSearch[exprLarge,{x,y,a},a!=0]*)


(* ::Input:: *)
(*exprRed0=# . #<=1&@{(x-1)/2,(y-3)/a,z}*)
(*exprLarge=Reduce[exprRed0,Reals]*)
(*RuleCanonicalDNFExpansion[exprLarge]//.$RuleReduceRationals*)
(*FullSimplify/@%*)
(*CanonicalizeSingleCandidateSearch[%,{x,y,z,a},a!=0]*)
(*CanonicalizeSingleCandidateSearch[exprLarge,{x,y,z,a},a!=0]*)
(*CanonicalizeSingleCandidateSearch[exprLarge,{x,y,z},a!=0]*)


(* ::Input:: *)
(*exprRed0=# . #==1&@{(x-1/2)/2,(y-3)/a,(z-4/3)/8}*)
(*exprLarge=Reduce[exprRed0,Reals]*)
(*RuleCanonicalDNFExpansion[exprLarge]//.$RuleReduceRationals*)
(*%//FullSimplify*)
(*CanonicalizeSingleCandidateSearch[%,{x,y,z,a},a!=0]*)


(* ::Section:: *)
(*Intersections*)


(* ::Input:: *)
(**)


(* ::Input:: *)
(*exprRed0=# . #-1<=0&[{(x-1/2)/2,y}]&&{x,y} . {1,1}>0*)
(*RegionPlot[ImplicitRegion[exprRed0,{x,y}]]*)
(*exprLarge=Reduce[exprRed0,Reals]*)
(*RuleCanonicalDNFExpansion[exprLarge]//.$RuleReduceRationals*)
(*%//FullSimplify*)
(*CanonicalizeSingleCandidateSearch[%,{x,y},a!=0]*)


(* ::Input:: *)
(*RegionPlot[1+4 Sqrt[1-y^2]>=2 x,{x,-1,2.5},{y,-1.5,1.5}]*)


(* ::Input:: *)
(*CanonicalizeSingleCandidateSearch[(15/4+x>=x^2+4 y^2&&y<1&&1+10 y>2 Sqrt[19]),{x,y}]*)


(* ::Input:: *)
(*exprRed0//Expand*)


(* ::Input:: *)
(*15/4+x>=x^2+4 y^2*)


(* ::Input:: *)
(*(* i is subset of (closed?) j: promissing ....*)*)
(*parts=List@@(RuleCanonicalDNFExpansion[exprLarge]//.$RuleReduceRationals);*)
(*(parts/.And->List)//MatrixForm*)
(*Outer[Reduce[#&&!#2]===False&,parts,parts/.{a_!=b_->Sequence[],Less->LessEqual,Greater->GreaterEqual}]*)


(* ::Input:: *)
(*(* promissing ....*)*)
(*Outer[Reduce[#&&!#2]===False&,List@@parts[[2]],List@@parts[[3]]]*)
(*Outer[Reduce[#&&!#2]===False&,List@parts[[2]],List@@parts[[3]]]*)
(*Outer[Reduce[#&&!#2]===False&,List@@parts[[2]],List@parts[[3]]]*)
(*Outer[Reduce[#&&!#2]===False&,List@parts[[3]],List@@parts[[2]]]*)


(* ::Input:: *)
(*parts=List@@(LogicalExpand[(RuleCanonicalDNFExpansion[exprLarge]//.$RuleReduceRationals)])*)
(*Outer[Reduce[#&&!#2,Reals]&,parts,parts]*)


(* ::Input:: *)
(*Reduce[1/4 (-(1/2)+x)^2+y^2<=1&&x+y>=0]*)


(* ::Input:: *)
(*exprRed0=# . #<=1&[{(x-1/2)/2,y}]&&{x,y} . {1,1}>=0*)
(*exprLarge=Reduce[exprRed0,Reals];*)
(*SimplifyAssuming[exprLarge,exprRed0[[1]]]*)
(*CanonicalizeSingleCandidateSearch[%,{x,y}]*)
(*SimplifyAssuming[exprLarge,exprRed0[[2]]]*)
(*CanonicalizeSingleCandidateSearch[%,{x,y}]*)


(* ::Input:: *)
(*CanonicalizeSingleCandidateSearch[expr_,varsAndParams_,assum_:True]:=Module[{*)
(*exprNoFrac=RuleCanonicalDNFExpansion[expr]*)
(*//.$RuleReduceRationals,*)
(*allSubExpr,candidateScores,feasibleCandidatePos,candidateScoreOrder,feasibleCandidates,bestCandidate*)
(*},*)
(*(* Look inside all And's & Or's in a logical expression and see if a single sub expression is equivalent to the whole thing under assum *)*)
(*allSubExpr=DeleteDuplicates@Flatten[exprNoFrac/.{Or->List,And->List}];*)
(*candidateScores=CountDistinct[Cases[#,Alternatives@@varsAndParams,Infinity]]&/@allSubExpr;*)
(*feasibleCandidatePos=Flatten@Position[candidateScores,x_/;x==Length@varsAndParams,1];*)
(*(* TODO: something with leaftcount and maybe OrderingBy *);*)
(*candidateScoreOrder=Ordering[-candidateScores[[feasibleCandidatePos]]];*)
(*feasibleCandidates=allSubExpr[[feasibleCandidatePos[[candidateScoreOrder]]]];*)
(*bestCandidate=SelectFirst[*)
(*feasibleCandidates,*)
(*SimplifyAssuming[*)
(*(* this Reduce typically requires fractions to be removed: `exprNoFrac` *)*)
(*Reduce[*)
(*Equivalent[#,exprNoFrac],*)
(*Reals],*)
(*assum]===True&*)
(*];*)
(*If[bestCandidate===Missing["NotFound"],expr,bestCandidate]*)
(*]*)


(* ::Input::Initialization:: *)
GenerateLogicalSubExtractor[expr_,allSubExpr_]:=Module[
{subExprPos,piece2PartComplement,id},
subExprPos=Position[expr,#,Infinity]&/@allSubExpr;
piece2PartComplement=AssociationMap[
Delete[Join@@subExprPos,#]&,Range@totalRegionCount];
ix|->Block[{Or,And},
(* this is annoying to write because And[Sequence[]] = True and Or[Sequence[]] = False, so just deleting the bad parts typically collapses SOP expression to True *)
SetAttributes[Or,Orderless];SetAttributes[And,Orderless];
ReplacePart[expr,(Intersection@@(piece2PartComplement/@ix))->id[]]/.{
And[w___id]->Sequence[],Or[w___id]:>Sequence[],Or[w__id,b___]:>Or[b],And[w__id,b___]:>And[b]
}
]
]


(* ::Input:: *)
(*exprRed0=# . #-1<=0&[{(x-1/2)/2,y}]&&{x,y} . {1,1}>0*)
(*expr=Reduce[exprRed0,Reals]*)
(*varsAndParams={x,y}*)
(*assum=True*)
(*(* see if RuleCanonicalDNFExpansion[exprLarge] is "smaller" - less large expressions, if it is, use that instead *)*)
(*expr=RuleCanonicalDNFExpansion[expr]*)
(*allSubExpr=DeleteDuplicates@Flatten[expr/.{Or->List,And->List}]*)
(*(*extractor=GenerateLogicalSubExtractor[expr,allSubExpr];*)*)
(*totalRegionCount=Length@allSubExpr;*)
(*candidateScores=CountDistinct[Cases[#,Alternatives@@varsAndParams,Infinity]]&/@allSubExpr*)
(*candidateScoreOrder=Ordering[-candidateScores]*)
(*(* start loop *)*)
(*candidateFound=False;*)
(*numRegions=1;*)
(*lowestVarCount=Length@varsAndParams;*)
(*While[!candidateFound&&lowestVarCount>0,*)
(*(* loop over region subsets, for each region: prioritize ones from other "Or" blocks *)*)
(*(* warning: below are not actually ordered *)*)
(*orderedRegions=Flatten@Position[candidateScores,x_/;x>=lowestVarCount];*)
(*numNVarRegions=Length[orderedRegions];*)
(**)
(*While[!candidateFound&&numRegions<=numNVarRegions,*)
(*tuples=SortBy[Tuples[Range[numNVarRegions],numRegions],Total];*)
(*bestCandidateIxs=SelectFirst[*)
(*tuples,*)
(*SimplifyAssuming[*)
(*(* this Reduce typically requires fractions to be removed: `exprNoFrac` *)*)
(*Reduce[*)
(*Equivalent[And@@allSubExpr[[orderedRegions[[#]]]],expr],*)
(*Reals],*)
(*assum]===True&*)
(*];*)
(*If[bestCandidateIxs=!=Missing["NotFound"],*)
(*candidateFound=True;*)
(*bestCandidateIxs=orderedRegions[[bestCandidateIxs]]*)
(*];*)
(*numRegions+=1;*)
(*];*)
(*lowestVarCount-=1;*)
(*]*)
(*If[candidateFound,*)
(*And@@allSubExpr[[bestCandidateIxs]],*)
(*expr*)
(*]*)


(* ::Input:: *)
(*expr*)


(* ::Input:: *)
(*allSubExpr*)


(* ::Input:: *)
(*PositionIndex[expr/.{Or->List,And->List}]*)


(* ::Input:: *)
(*expr*)


(* ::Input:: *)
(*Intersection@@(piece2PartComplement/@{2,1})*)


(* ::Input:: *)
(*Extract[expr,{{2,2},{3,1}}]*)


(* ::Input:: *)
(*expr[[{2,2},{3,1}]]*)


(* ::Input:: *)
(*Delete[expr,{{2,2},{3,1}}]*)


(* ::Input:: *)
(*expr=RuleCanonicalDNFExpansion[expr]*)
