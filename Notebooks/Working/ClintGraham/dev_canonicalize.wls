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

RuleCanonicalDNFExpansion[expr_]:=Module[{f,g},Block[{Plus},
SetAttributes[Plus,Orderless];
SetAttributes[f,Orderless];
SetAttributes[g,Orderless];
((LogicalExpand/@BooleanMinimize[exprLarge,"DNF"])
//.$RuleGreaterInnequalities
//.{
Or->f,And->g,
a_==b_:>h[a,b,0],a_>=b_:>h[a,b,1],a_>b_:>h[a,b,2]
}
//.{
(* De-Reduce innequalities *)
f[u___,
g[b_>a_,t___],
g[a_>b_,y___]
]/;g[t]===g[y]
:>f[g[a!=b,t],u],

(* De-Reduce quadratics *)
a_>=d_+b_ Sqrt[c_]:>a-d>=b Sqrt[c],
d_+b_ Sqrt[c_]>=a_:>b Sqrt[c]>=a-d,
a_>d_+b_ Sqrt[c_]:>a-d>b Sqrt[c],
d_+b_ Sqrt[c_]>a_:>b Sqrt[c]>a-d,
a_==d_+b_ Sqrt[c_]:>a-d==b Sqrt[c],
d_+b_ Sqrt[c_]==a_:>b Sqrt[c]==a-d,

f[u___,
g[a_>=b_. Sqrt[c_],t___],
g[d_. Sqrt[c_]>=a_,y___]
]
/;b==-d&&g[t]===g[y]
:>f[g[b^2 c>=a^2,t],u],
f[u___,
g[a_>b_. Sqrt[c_],t___],
g[d_. Sqrt[c_]>a_,y___]
]
/;b==-d&&g[t]===g[y]
:>f[g[b^2 c>a^2,t],u]
(*^ Need to figure out how to succinctly write strictly greater here too *),

g[a_>=b_. Sqrt[c_],d_. Sqrt[c_]>=a_,y___]
/;b==-d
:>g[b^2 c>=a^2,y],
g[a_>b_. Sqrt[c_],d_. Sqrt[c_]>a_,y___]
/;b==-d
:>g[b^2 c>a^2,y],

f[u___,
g[a_>=b_. Sqrt[c_],0>a,t___],
g[d_. Sqrt[c_]>=a_,a>0,y___]
]
/;b==-d&&g[t]===g[y]
:>f[g[a^2>=b^2 c,t],u],
f[u___,
g[b_. Sqrt[c_]==a_,t___],
g[d_. Sqrt[c_]==a_,y___]
]
/;b==-d&&g[t]===g[y]
:>f[g[a^2==b^2 c,t],u]

(*f[u___,
g[p_,t___],
g[q_,y___]
]
/;q==!p&&g[t]===g[y]
:>f[g[t,y],u]*)
}
)//.{f->Or,g->And}
]]


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
(*exprRed0=# . #<=1&@{(x-1)/2,(y-3)/a,z}*)
(*exprLarge=Reduce[exprRed0,Reals];*)
(*RuleCanonicalDNFExpansion[exprLarge]*)
(*%//.$RuleReduceRationals//FullSimplify*)


(* ::Section:: *)
(*CanonicalizeSingleCandidateSearch*)


(* ::Input::Initialization:: *)
Clear[CanonicalizeSingleCandidateSearch]

CanonicalizeSingleCandidateSearch[expr_,varsAndParams_,assum_:True]:=Module[{
exprNoFrac=RuleCanonicalDNFExpansion[exprLarge]
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
assum]&
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



