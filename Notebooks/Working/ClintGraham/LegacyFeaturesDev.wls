#!/usr/bin/env wolframscript
(* ::Package:: *)

ResourceFunction["DarkMode"][]
PacletDirectoryLoad[Nest[ParentDirectory,NotebookDirectory[],3]]
<<ConvexAnalysisGeometry`


(* ::Section::Closed:: *)
(*ELVIS*)


<<ConvexAnalysisGeometry`Legacy`Elvis`


(* ::Input:: *)
(*First@Timing@Quiet@defVel[F0,{{-1,-1},{-1,1},{1,-1},{1,1},{2,0},{-1.5,0}}]*)
(*First@Timing@Quiet@defVel[F1,1.5{{0,1},{1,0},{0,-1},{-1,0}}]*)
(*GraphicsRow[LabeledPolarHullPlot/@{F0,F1}]*)


(* ::Input:: *)
(*Show[Graphics[{*)
(*Arrowheads[Small],*)
(*Table[*)
(*Module[{x0={0,-2},T=4,t=-.1,y0,v0,\[Zeta]0,\[Zeta]2s,v2s},*)
(*y0={t0,0};*)
(*t=Subscript[\[Gamma], F0][y0-x0];*)
(*v0=(y0-x0)/t;*)
(*(* Choose \[Zeta]0 \[Element] Subscript[N, F0](v0) *)*)
(*\[Zeta]0=Subscript[\!\(\*OverscriptBox[\(\[ScriptCapitalN]\), \(^\)]\), F0][v0](* points in normal cone properly scaled *);*)
(*(* calculate refracted angles with optimality conditions *)*)
(*\[Zeta]2s=Subscript[RefractedNormals, F1][\[Zeta]0];*)
(*v2s=Select[discretize/@Subscript[\!\(\*OverscriptBox[\(\[ScriptCapitalN]\), \(^\)]\), (F1^\[Degree])]/@\[Zeta]2s,NonNegative@Last@#&];*)
(**)
(**)
(*If[T>Subscript[\[Gamma], F0][y0-x0],*)
(*{Black,Line[{x0,y0}],Tooltip[Arrow[{y0,(y0+(T-Subscript[\[Gamma], F0][y0-x0])#)}],{v0}]},*)
(*{Lighter@Gray,Line[{x0,y0}]}*)
(*]&/@v2s*)
(**)
(*],*)
(*{t0,-6,6,0.5}*)
(*]}]]*)


(* ::Section:: *)
(*FCC*)


<<ConvexAnalysisGeometry`Legacy`FCC`


(* ::Subsection::Closed:: *)
(*dev_pwl*)


(* ::Input:: *)
(*fpwl=pwl[{{-1,3},{0,0},{1,1}}]*)
(**)
(*fpwlFun=pwl2fun@fpwl;*)
(*{fpwlFun,Plot[fpwlFun[x],{x,-1,1}]}*)


(* ::Input:: *)
(*infconv[(x-2)^2,pwl[{{-1,3},{0,0},{1,1}}],x]*)
(*Plot[%,{x,-2.7`,5.7`}]*)


(* ::Input:: *)
(*slfc[pwl[{{-1,1},{0,0},{1,1},{2,3}}],x]*)


pwl2Fun0[pwl["max",{{3c,-2},{5,4},{5,-4}},{3,6/c,0}]][x,y]
Manipulate[
 Plot3D[%,{x,-2,2},{y,-2,2}],{c,-1,1}]


(* ::Subsection:: *)
(*FCC Demo*)


(* ::Input:: *)
(*Lxv=x^2/2+ind[x,x,{-1,1}]+Abs[v]*)
(*slfc[Lxv,{x,v}]*)
(*%//TraditionalForm*)


(* ::Input:: *)
(*L1x=Lxv[[{1,3}]]*)
(*L2v=Lxv[[2]]*)


(* ::Input:: *)
(*Myw=slfc[Lxv,{x,v}]/.*)
(*{slfc[v]->y,slfc[x]->w};*)
(*Myw//TraditionalForm*)


(* ::Input:: *)
(*M1y=Myw[[1]]*)
(*M2w=Myw[[2]]*)


(* ::Input:: *)
(*huber[x_]:=x^2/(2\[Lambda]);*)


(* ::Subsubsection:: *)
(*Subscript[e, \[Lambda]]Subscript[M, 1][y]*)


(* ::Input:: *)
(*M1y//TraditionalForm*)


(* ::Input:: *)
(*meM1y=infconv[huber[y],M1y,y]*)


(* ::Subsubsection:: *)
(*Subscript[e, \[Lambda]]Subscript[L, 2][v]*)


(* ::Input:: *)
(*L2v//TraditionalForm*)


(* ::Input:: *)
(*meL2v=infconv[huber[v],L2v,v]*)


(* ::Subsubsection:: *)
(*Subscript[e, \[Lambda]]Subscript[L, 1][x]*)


(* ::Input:: *)
(*L1x//TraditionalForm*)


(* ::Input:: *)
(*meL1x=infconv[huber[v],L1x,v]*)


(* ::Text:: *)
(*That didn't work... New strategy:*)
(**)
(*(f+Subscript[\[Delta], R])\[Placeholder] h = \!\(\*SuperscriptBox[\((\((f + *)
(*\*SubscriptBox[\(\[Delta]\), \(R\)])\) \[Placeholder]  h)\), \(**\)]\) = SuperStar[((SuperStar[f] \[Placeholder] SuperStar[Subscript[\[Delta], R]])+SuperStar[h])]*)
(**)


(* ::Input:: *)
(*meL1xConj=infconv[*)
(*slfc[x^2/2,x],*)
(*slfc[ind[x,x,{-1,1}],x],slfc[x]*)
(*]+slfc[x^2/(2\[Lambda]),x];*)
(*%//TraditionalForm*)


(* ::Input:: *)
(*$Assumptions=\[Lambda]>0;*)
(*meL1xConj=infconv[slfc[x^2/2,x],slfc[ind[x,x,{-1,1}],x],slfc[x]]+slfc[x^2/(2\[Lambda]),x];*)
(*%//TraditionalForm*)


(* ::Input:: *)
(*meL1x=slfc[meL1xConj,slfc[x]];*)
(*%//TraditionalForm*)
(*meL1x=meL1x/.{slfc[slfc[x_]]:>x}//FullSimplify;*)
(*%//TraditionalForm*)


(* ::Text::Initialization:: *)
(*Note the complicated redundant terms above...*)


(* ::Subsubsection:: *)
(*Subscript[e, \[Lambda]]Subscript[M, 2][w]*)


(* ::Input:: *)
(*M2w//TraditionalForm*)


(* ::Input:: *)
(*meM2w=infconv[huber[y],M2w,y]*)


(* ::Text:: *)
(*That didn't work... New strategy:*)
(**)
(*f \[Placeholder] h = \!\(\*SuperscriptBox[\((f  \[Placeholder]  h\ )\), \(**\)]\) = SuperStar[(SuperStar[f]+SuperStar[h])]*)
(**)


(* ::Input:: *)
(*M2wConj =slfc[M2w,w]//FullSimplify*)


(* ::Input:: *)
(*M2wConj =slfc[w]^2/2+ind[slfc[w],slfc[w],{-2,2}];*)
(*%//TraditionalForm*)


(* ::Input:: *)
(*meM2wConj=M2wConj+slfc[huber[w],w];*)
(*%//TraditionalForm*)
(*meM2w=slfc[meM2wConj,slfc[w]];*)
(*%//TraditionalForm*)
(*meM2w=meM2w/.{slfc[slfc[x_]]:>x}//FullSimplify;*)
(*%//TraditionalForm*)


(* ::Subsubsection:: *)
(*Goebel Envelopes*)


(* ::Input:: *)
(*geL1x=(1-\[Lambda])^2(meL1x)+\[Lambda] x^2/2//PiecewiseExpand//FullSimplify;*)
(*geL2v=(1-\[Lambda])^2(meL2v)+\[Lambda] v^2/2//PiecewiseExpand//FullSimplify;*)
(*geM1y=(1-\[Lambda])^2(meM1y)+\[Lambda] y^2/2//PiecewiseExpand//FullSimplify;*)
(*geM2w=(1-\[Lambda])^2(meM2w)+\[Lambda] w^2/2//PiecewiseExpand//FullSimplify*)


(* ::Subsubsection:: *)
(*Hamiltonian trajectories*)


(* ::Input:: *)
(*meH=geM1y-geL1x(*rename to geH*)*)


(* ::Input:: *)
(*bnd=5;*)
(*Manipulate[Plot3D[Evaluate[meH/.\[Lambda]->\[Lambda]0],{x,-bnd,bnd},{y,-bnd,bnd},PlotRange->{-bnd,bnd}],{{\[Lambda]0,0.5},0.00001,2}]*)


(* ::Input:: *)
(*bnd=5;*)
(*Manipulate[ContourPlot[Evaluate[meH/.\[Lambda]->\[Lambda]0],{y,-bnd,bnd},{x,-bnd,bnd},PlotRange->{-bnd,bnd}],{{\[Lambda]0,0.5},0.00001,2}]*)
