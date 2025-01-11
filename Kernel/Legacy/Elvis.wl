(* ::Package:: *)


Package["ConvexAnalysisGeometry`Legacy`Elvis"];


(* ::Section:: *)
(*Utils*)


(* ::Subsection:: *)
(*Usage Tools*)


(* ::Input::Initialization:: *)
SnellPalette[] := CreatePalette[Grid[Partition[PasteButton[RawBoxes[#], ImageSize -> {30, 30}, Appearance -> "FramedPalette"]& /@ {
        "\!\(\*SubscriptBox[\(\[SelectionPlaceholder]\), \(\[Placeholder]\)]\)", "\!\(\*SubscriptBox[SuperscriptBox[\(\[SelectionPlaceholder]\), \(\[Degree]\)], \(\[Placeholder]\)]\)", "\!\(\*SubscriptBox[\(\[Gamma]\), \(\[SelectionPlaceholder]\)]\)", "\!\(\*SubscriptBox[\(\[Sigma]\), \(\[SelectionPlaceholder]\)]\)"
      }, UpTo[2]], Spacings -> {0, .1}]];


(* ::Subsection:: *)
(*Geometric Definitions*)


(* ::Input::Initialization:: *)
\[ScriptCapitalR][t_] := {{Cos[t], - Sin[t]}, {Sin[t], Cos[t]}}; r90 = \[ScriptCapitalR][\[Pi]/2];
rotationNormals[pts_] := Map[r90 . #&, pts - RotateLeft @ pts](* assumes positivelyOrient applied to pts *)

normalize[v_] := v/Norm[v]

atan2[y_, x_] := \!\(\*
  TagBox[GridBox[{
        {"\[Piecewise]", GridBox[{
              {
                RowBox[{"ArcTan", "[",
                    RowBox[{"y", "/", "x"}], "]"}],
                RowBox[{"x", ">", "0"}]},
              {
                RowBox[{
                    RowBox[{"ArcTan", "[",
                        RowBox[{"y", "/", "x"}], "]"}], " ", "+", " ", "\[Pi]"}],
                RowBox[{
                    RowBox[{"x", "<", "0"}], " ", " && ", " ",
                    RowBox[{"y", " ", " >= ", " ", "0"}]}]},
              {
                RowBox[{
                    RowBox[{"ArcTan", "[",
                        RowBox[{"y", "/", "x"}], "]"}], " ", "-", " ", "\[Pi]"}],
                RowBox[{
                    RowBox[{"x", "<", "0"}], " ", " && ", " ",
                    RowBox[{"y", "<", "0"}]}]},
              {
                RowBox[{"\[Pi]", "/", "2"}],
                RowBox[{
                    RowBox[{"x", " ", " == ", " ", "0"}], " ", " && ", " ",
                    RowBox[{"y", ">", "0"}]}]},
              {
                RowBox[{" ",
                    RowBox[{
                        RowBox[{"-", " ", "\[Pi]"}], "/", "2"}]}],
                RowBox[{
                    RowBox[{"x", " ", " == ", " ", "0"}], " ", " && ", " ",
                    RowBox[{"y", "<", "0"}]}]},
              {
                RowBox[{"Undefined", "[", "]"}],
                RowBox[{
                    RowBox[{"x", " ", " == ", " ", "0"}], " ", " && ", " ",
                    RowBox[{"y", " ", " == ", " ", "0"}]}]}
            },
            AllowedDimensions -> {2, Automatic},
            Editable -> True,
            GridBoxAlignment -> {"Columns" -> {{Left}}, "ColumnsIndexed" -> {}, "Rows" -> {{Baseline}}, "RowsIndexed" -> {}},
            GridBoxItemSize -> {"Columns" -> {{Automatic}}, "ColumnsIndexed" -> {}, "Rows" -> {{1.}}, "RowsIndexed" -> {}},
            GridBoxSpacings -> {"Columns" -> {Offset[0.27999999999999997`], {Offset[0.84]}, Offset[0.27999999999999997`]}, "ColumnsIndexed" -> {}, "Rows" -> {Offset[0.2], {Offset[0.4]}, Offset[0.2]}, "RowsIndexed" -> {}},
            Selectable -> True]}
      },
      GridBoxAlignment -> {"Columns" -> {{Left}}, "ColumnsIndexed" -> {}, "Rows" -> {{Baseline}}, "RowsIndexed" -> {}},
      GridBoxItemSize -> {"Columns" -> {{Automatic}}, "ColumnsIndexed" -> {}, "Rows" -> {{1.}}, "RowsIndexed" -> {}},
      GridBoxSpacings -> {"Columns" -> {Offset[0.27999999999999997`], {Offset[0.35]}, Offset[0.27999999999999997`]}, "ColumnsIndexed" -> {}, "Rows" -> {Offset[0.2], {Offset[0.4]}, Offset[0.2]}, "RowsIndexed" -> {}}],
    "Piecewise",
    DeleteWithContents -> True,
    Editable -> False,
    SelectWithContents -> True,
    Selectable -> False,
    StripWrapperBoxes -> True]\)
atan2[{x_, y_}] := atan2[y, x]

positivelyOrient[pts_] := SortBy[pts, atan2, Less]


(* ::Input::Initialization:: *)
lineThroughPointsEqu[{{x1_, y1_}, {x2_, y2_}}] := y - y1 == ((y2 - y1) (x - x1))/(x2 - x1);
lineThroughPointsYFunc[{{x1_, y1_}, {x2_, y2_}}] := Function[{x}, ((y2 - y1) (x - x1))/(x2 - x1) + y1]
lineThroughPointsRFunc[{{x1_, y1_}, {x2_, y2_}}] := Module[
  {r1 = Norm[{x1, y1}], \[Theta]1 = atan2[y1, x1], \[Theta]0 = Piecewise[{{ArcTan[(y2 - y1)/(x2 - x1)], x1! = x2}, {\[Pi]/2, True}}]}, Function[{\[Theta]}, (r1 Sin[\[Theta]1 - \[Theta]0])/Sin[\[Theta] - \[Theta]0]]]


(* ::Subsection:: *)
(*Cones*)


(* ::Input::Initialization:: *)
ConeQ[x_] := !FreeQ[x, \[Lambda]]

DF = 5;
discretize[x_] := If[ConeQ[x],
  Sequence @@ Table[x /. \[Lambda] -> t, {t, 0, 1, 1/(DF - 1)}], x]


(* ::Subsection:: *)
(*Ellipses*)


(* ::Input::Initialization:: *)
ClosedFormEllipse[F_, npts_:10] := Module[{ellipseParam, comparableParam, ptsComp, pts, errors, mse, optRep, plot},
  Clear[t1, a, b, t, c1, c2];
  ellipseParam = \[ScriptCapitalR][t1] . {a Cos[t], b Sin[t]} + {c1, c2};
  comparableParam = ellipseParam/(Subscript[\[Gamma], F][{x, y}] /. Thread[{x, y} -> ellipseParam])//FullSimplify;
  ptsComp = Table[comparableParam, {t, 0, 2\[Pi], 2\[Pi]/(npts - 1)}];
  pts = Table[ellipseParam, {t, 0, 2\[Pi], 2\[Pi]/(npts - 1)}];
  errors = Flatten[ptsComp - pts];
  {mse, optRep} = FindMinimum[{Mean[errors^2], {0<a, 0<b, 0 <= t1<2\[Pi]}}, {{a, 1}, {b, 1}, {c1, 0}, {c2, 0}, {t1, 0}}, Method -> "InteriorPoint"];
  plot = ParametricPlot[{Subscript[(F), bdryParam], ellipseParam /. optRep}, {t, 0, 2\[Pi]}, PlotStyle -> {Thick, Directive[{Red, Dashed}]}];
  {mse, optRep, plot}
]


(* ::Subsection:: *)
(*Extending Notation*)


(* ::Input::Initialization:: *)
BoundaryConditions[F_] := Subscript[F, bdryCnds]
BoundaryParamerterization[F_] := Subscript[F, bdryParam]
Support[F_] := Subscript[\[Sigma], F]
Gauge[F_] := Subscript[\[Gamma], F]
Polar[F_] := F^\[Degree]
NormalizedNormalCone[F_] := Subscript[\!\(\*OverscriptBox[\(\[ScriptCapitalN]\), \(^\)]\), F]
RefractedNormals[F_] := Subscript[RefractedNormals, F]


(* ::Section:: *)
(*defVel*)


(* ::Subsection:: *)
(*defVel (implicit)*)


(* ::Input::Initialization:: *)
Options[defVel] = {"DeriveParametricEquation" -> True};
defVel[F_Symbol, def_Equal, OptionsPattern[]] := Module[{}, Off[Part::partd];Subscript[F, bdryCnds] = def;Subscript[\[Sigma], F] = Function[{v}, Evaluate[Simplify[
        FullSimplify[Evaluate[Max[
              {v[[1]], v[[2]]} . {x, y} /. 
              Solve[
                Eliminate[
                  \!\(
                    \*SubscriptBox[\(\[PartialD]\), \({{x, y, \[Lambda]}}\)]\(({v[\([\)\(1\)\(]\)], v[\([\)\(2\)\(]\)]} . {x, y} - \[Lambda]\ \((#1[\([\)\(2\)\(]\)] - #1[\([\)\(1\)\(]\)] &)\)[
                          \*SubscriptBox[\(F\), \(bdryCnds\)]])\)\) = 0,
                  \[Lambda]],
                {x, y}]
        ]]],
        (v[[1]]|v[[2]])\[Element]Reals]]];
  Subscript[\[Gamma], F^\[Degree]] = Subscript[\[Sigma], F];
  Subscript[\!\(\*OverscriptBox[\(\[ScriptCapitalN]\), \(^\)]\), F^\[Degree]] = Function[{\[Zeta]}, Evaluate[Grad[Subscript[\[Gamma], (F^\[Degree])][{x, y}], {x, y}] /. {x -> \[Zeta][[1]], y -> \[Zeta][[2]]}]];
  
  Subscript[F^\[Degree], bdryCnds] = Subscript[\[Gamma], (F^\[Degree])][{x, y}] == 1;Subscript[\[Sigma], F^\[Degree]] = Function[{\[Zeta]}, Evaluate[Simplify[
        FullSimplify[Evaluate[Max[
              {\[Zeta][[1]], \[Zeta][[2]]} . {x, y} /. 
              Solve[Eliminate[\!\(
                    \*SubscriptBox[\(\[PartialD]\), \({{x, y, \[Lambda]}}\)]\(({\[Zeta][\([\)\(1\)\(]\)], \[Zeta][\([\)\(2\)\(]\)]} . {x, y} - \[Lambda]\ \((#1[\([\)\(2\)\(]\)] - #1[\([\)\(1\)\(]\)] &)\)[
                          \*SubscriptBox[
                            SuperscriptBox[\(F\), \(\[Degree]\)], \(bdryCnds\)]])\)\) == 0, \[Lambda]], {x, y}]]]],
        (\[Zeta][[1]]|\[Zeta][[2]])\[Element]Reals]]];
  Subscript[\[Gamma], F] = Subscript[\[Sigma], F^\[Degree]];
  Subscript[\!\(\*OverscriptBox[\(\[ScriptCapitalN]\), \(^\)]\), F] = Function[{v}, Evaluate[Grad[Subscript[\[Gamma], F][{x, y}], {x, y}] /. {x -> v[[1]], y -> v[[2]]}]];
  
  Subscript[RefractedNormals, F] = Function[{\[Zeta]},
    Evaluate[({\[Zeta][[1]], #1}&) /@ DeleteCases[
        Last /@ First /@ Solve[N[Subscript[F^\[Degree], bdryCnds]], {y}, Reals] /. {x -> \[Zeta][[1]]},
        Undefined]]
  ];
  
  If[OptionValue[DeriveParametricEquation],
    sol = Solve[{Subscript[F, bdryCnds], Cos[t] y == Sin[t] x}, {x, y}, Reals];
    If[Length[sol] == 2,
      Subscript[F, bdryParam] = Simplify[Piecewise[Transpose[{{x, y} /. sol, {\[Pi] <= t <= 2 \[Pi], 0 <= t<\[Pi]}}]]],
      Subscript[F, bdryParam] = {x, y} /. sol]
  ];
  On[Part::partd];
]
defVel[F_Symbol, def_LessEqual] := defVel[F, def /. {LessEqual -> Equal}]


(* ::Subsection:: *)
(*defVel (parametric)*)


(* ::Input::Initialization:: *)
defVel[F_Symbol, def_List /; (Length[def] == 2)] := Module[{},
  (*Off /@ {Part::partd, Eliminate::ifun, Solve::ratnz};*)
  (* def given is parameterization of bdry(F) in rectangular coordinates *)
  Subscript[F, bdryParam] = def;
  (* the projective 'dual curve' corresponds to the polar bdry in \[DoubleStruckCapitalR]^2 (easy check) *)
  Subscript[F^\[Degree], bdryParam] = - Simplify @ {
    \!\(
      \*SubscriptBox[\(\[PartialD]\), \(t\)]\((def[\([\)\(2\)\(]\)])\)\)/(def[[2]]*\!\(
        \*SubscriptBox[\(\[PartialD]\), \(t\)]\((def[\([\)\(1\)\(]\)])\)\) - def[[1]]*\!\(
        \*SubscriptBox[\(\[PartialD]\), \(t\)]\((def[\([\)\(2\)\(]\)])\)\)), \!\(
      \*SubscriptBox[\(\[PartialD]\), \(t\)]\((def[\([\)\(1\)\(]\)])\)\)/(def[[1]]*\!\(
        \*SubscriptBox[\(\[PartialD]\), \(t\)]\((def[\([\)\(2\)\(]\)])\)\) - def[[2]]*\!\(
        \*SubscriptBox[\(\[PartialD]\), \(t\)]\((def[\([\)\(1\)\(]\)])\)\))};
  
  
  (* derive implicit definition *)
  Subscript[F, bdryCnds] = FullSimplify @ Eliminate[Subscript[F, bdryParam][[1]] == x && Subscript[F, bdryParam][[2]] == y, t];
  defVel[F, Subscript[F, bdryCnds], "DeriveParametricEquation" -> False]
  (*On /@ {Part::partd, Eliminate::ifun, Solve::ratnz};*)
]


(* ::Subsection:: *)
(*defVel (finitely generated)*)


(* ::Subsubsection::Closed:: *)
(*Definition*)


(* ::Input::Initialization:: *)
defVel[F_Symbol, def_List /; (Length[def] >= 3)] := Module[{normals, \[Degree]normals},
  (* define velocity set by points in \[DoubleStruckCapitalR]^2 *)
  Subscript[F, pt] = positivelyOrient[def];
  normals = rotationNormals[Subscript[F, pt]];
  Subscript[F, cnds] = Simplify[normals[[#]] . {x, y} <= normals[[#]] . Subscript[F, pt][[#]]& /@ Range[Length[normals]]];
  Subscript[F, reg] = ImplicitRegion[Subscript[F, cnds], {x, y}];
  
  Subscript[F, \[Theta]Mag] = hullMagFunc[Subscript[F, pt]];
  (*Subscript[\[Gamma], F] = Compile[{{x, _Real, 1}}, Norm[x]/Subscript[F, \[Theta]Mag][atan2[x]]];*)
  Subscript[\[Gamma], F] = Function[{x}, Evaluate @ Simplify[
      Max[#1 . x/#1 . #2& @@@ ({rotationNormals[Subscript[F, pt]], Subscript[F, pt]}\[Transpose])]
  ]];
  Subscript[F, v\[Zeta]] = v\[Zeta]Link[F];
  Subscript[\!\(\*OverscriptBox[\(\[ScriptCapitalN]\), \(^\)]\), F] = Subscript[F, v\[Zeta]][atan2[{#[[1]], #[[2]]}]]&;
  
  Subscript[F, v\[Zeta]Disp] = Thread[rotatedPairs[Range[4]] -> Range[4]]~Join~Thread[Range[4] -> RotateRight @ rotatedPairs[Range[4]]](* v\[Rule]\[Zeta] *);
  Subscript[F^\[Degree], pt] = hullToPolar[Subscript[F, pt]];
  \[Degree]normals = rotationNormals[Subscript[F^\[Degree], pt]];
  Subscript[F^\[Degree], cnds] = Simplify[\[Degree]normals[[#]] . {x, y} <= \[Degree]normals[[#]] . Subscript[(F^\[Degree]), pt][[#]]& /@ Range[Length[\[Degree]normals]]];
  Subscript[F^\[Degree], reg] = ImplicitRegion[Subscript[F^\[Degree], cnds], {x, y}];
  
  Subscript[F^\[Degree], \[Theta]Mag] = hullMagFunc[Subscript[F^\[Degree], pt]];
  Subscript[F, \[Zeta]v] = \[Zeta]vLink[F];
  Subscript[\!\(\*OverscriptBox[\(\[ScriptCapitalN]\), \(^\)]\), F^\[Degree]] = If[ConeQ[#], Subscript[F, \[Zeta]v][atan2[# /. \[Lambda] -> 0.5]], Subscript[F, \[Zeta]v][atan2[{#[[1]], #[[2]]}]]]&;
  
  Subscript[RefractedNormals, F] = Function[{\[Zeta]},
    (* input: incident normal cone \[Zeta] / output: reflected normal cone *)
    Module[{optVels = Subscript[F^\[Degree], pt], optCones = (SortBy[#, First]& /@ rotatedPairs[#])&[Subscript[F^\[Degree], pt]]},
      If[ConeQ[\[Zeta]],
        (* \[Zeta]0 is a cone *)
        With[{\[Zeta]0 = SortBy[{\[Zeta] /. \[Lambda] -> 0, \[Zeta] /. \[Lambda] -> 1}, First](* temporary *)},
          optVels = Select[optVels, \[Zeta]0[[1, 1]] <= #[[1]] <= \[Zeta]0[[02, 1]]&];
          optCones = Select[optCones, - #[[2, 1]] <= \[Zeta]0[[1, 1]] <= \[Zeta]0[[2, 1]] <= - #[[1, 1]] || Not[Intersection[#, optVels] === {}]&];
        ],
        (* \[Zeta] is not a cone *)
        optVels = Select[optVels, #[[1]] == \[Zeta][[1]]&];
        optCones = Select[optCones, #[[1, 1]]<\[Zeta][[1]]<#[[2, 1]] || \[Zeta][[1]] == #[[1, 1]] == #[[2, 1]]&]
      ];
      optVels~Join~(\[Lambda] #1 + (1 - \[Lambda])#2& @@@ optCones)
    ]
  ];
  Subscript[RefractedVelocities, F] = Function[{\[Zeta], n}, With[{\[Theta] = N @ VectorAngle[n, {0, 1}]},
      (* input: incident normal cone \[Zeta] & normal vect to incident plane / output: reflected velocity *)
      Module[{optVecs = \[ScriptCapitalR][\[Theta]] . #& /@ Subscript[(F^\[Degree]), pt], optCones = SortBy[#, First]& /@ rotatedPairs[\[ScriptCapitalR][\[Theta]] . #& /@ Subscript[(F^\[Degree]), pt]]},
        If[ConeQ[\[Zeta]],
          (* \[Zeta]0 is a cone *)
          Block[{\[Zeta]0 = \[ScriptCapitalR][\[Theta]] . \[Zeta]},
            \[Zeta]0 = SortBy[{# /. \[Lambda] -> 0, # /. \[Lambda] -> 1}& @ \[Zeta]0, First&](* temporary *);
            optVecs = Select[optVecs, \[Zeta]0[[1, 1]] <= - #[[1]] <= \[Zeta]0[[02, 1]]&];
            optCones = Select[optCones, - #[[2, 1]] <= \[Zeta]0[[1, 1]] <= \[Zeta]0[[2, 1]] <= - #[[1, 1]] || Not[Intersection[#, optVecs] === {}]&];
          ],
          (* \[Zeta] is not a cone *)
          With[{\[Zeta]0 = \[ScriptCapitalR][\[Theta]] . \[Zeta]},
            optVecs = Select[optVecs, #[[1]] == \[Zeta]0[[1]]&];
            optCones = Select[optCones, #[[1, 1]]<\[Zeta]0[[1]]<#[[2, 1]] || \[Zeta]0[[1]] == #[[1, 1]] == #[[2, 1]]&]
          ]
        ];
        \[ScriptCapitalR][ - \[Theta]] . #& /@ Subscript[\!\(\*OverscriptBox[\(\[ScriptCapitalN]\), \(^\)]\), (F^\[Degree])] /@ Join[optVecs, (\[Lambda] #1 + (1 - \[Lambda])#2& @@@ optCones)]
      ]
  ]];
]
clearVel[F_Symbol] := Do[v = ., {v, {Subscript[F, pt], Subscript[F, ineq], Subscript[F, reg], Subscript[F^\[Degree], pt], Subscript[F^\[Degree], ineq], Subscript[F^\[Degree], reg]}}]


(* ::Subsubsection:: *)
(*Geometric Definitions*)


(* ::Input::Initialization:: *)
rotatedPairs[pts_] := Partition[pts, 2, 1, 1]
hullMagFunc[pts_] := Function[{\[Theta]},
  (* defines piecewise function for the magnitude of a convex hull (containing the origin) in the direction \[Theta] *)
  Piecewise[{#2[\[Theta]], If[#1[[1]] <= #1[[2]], #1[[1]] <= \[Theta]<#1[[2]], - #1[[1]] <= \[Theta]<#1[[2]]]}& @@@ (
      {rotatedPairs[atan2 /@ pts], lineThroughPointsRFunc[#]& /@ rotatedPairs[pts]}\[Transpose])]]


(* ::Input::Initialization:: *)
hullToPolar[hull_] := {(#1[[2]] - #2[[2]])/(#1[[2]] #2[[1]] - #1[[1]] #2[[2]]), (#1[[1]] - #2[[1]])/( - #1[[2]] #2[[1]] + #1[[1]] #2[[2]])}& @@@ Partition[hull~Append~First @ hull, 2, 1]


(* ::Input::Initialization:: *)
getThetaCnds[{p1_List, p2_List}] := If[atan2[p1]<atan2[p2], atan2[p1]<\[Theta]<atan2[p2], atan2[p1]<\[Theta]<atan2[p2] + 2\[Pi]]
getThetaCnds[p1_] := (\[Theta] == atan2[p1])
(* TODO: make proper dictionary *)
v\[Zeta]Link[F_] := Function[{th}, Piecewise[{Subscript[(F^\[Degree]), pt]~Join~(\[Lambda] #1 + (1 - \[Lambda])#2& @@@ RotateRight @ rotatedPairs[Subscript[F^\[Degree], pt]]), getThetaCnds /@ (rotatedPairs[Subscript[F, pt]]~Join~Subscript[F, pt])}\[Transpose]] /. {\[Theta] -> th}]
\[Zeta]vLink[F_] := Function[{th}, Piecewise[{RotateLeft @ Subscript[F, pt]~Join~(\[Lambda] #1 + (1 - \[Lambda])#2& @@@ rotatedPairs[Subscript[F, pt]]), getThetaCnds /@ (rotatedPairs[Subscript[F^\[Degree], pt]]~Join~Subscript[(F^\[Degree]), pt])}\[Transpose]] /. {\[Theta] -> th}]


(* ::Input::Initialization:: *)
ConeQ[x_] := !FreeQ[x, \[Lambda]]

DF = 5;
discretize[x_] := If[ConeQ[x],
  Sequence @@ Table[x /. \[Lambda] -> t, {t, 0, 1, 1/(DF - 1)}], x]


(* ::Subsubsection:: *)
(*Plot Definitions*)


(* ::Input::Initialization:: *)
PolarHullPlot[F_, styles___] := Graphics[{
    Blue, Thick, Line[{#1, #2}]& @@@ rotatedPairs[Subscript[F^\[Degree], pt]],
    Purple, Arrow[{{0, 0}, #}]& /@ (Subscript[F^\[Degree], pt]),
    Line[{#1, #2}]& @@@ rotatedPairs[Subscript[F, pt]],
    Blue, PointSize[Large], Point /@ (Subscript[F, pt]),
    Gray, Thin, Dashed, Circle[]
  }, styles]
SmallPolarHullPlot[F_, styles___] := Graphics[{
    Blue, Thick, Line[{#1, #2}]& @@@ rotatedPairs[Subscript[F^\[Degree], pt]],
    Purple, PointSize[Large], Point /@ (Subscript[F^\[Degree], pt]), Line[{#1, #2}]& @@@ rotatedPairs[Subscript[F, pt]],
    Blue, Point /@ (Subscript[F, pt]),
    Gray, Thin, Dashed, Circle[]
  }, styles]
LabeledPolarHullPlot[F_, styles___Rule] := Show[{
    PolarHullPlot[F],
    ListPlot[Join[
        Callout[#1, Subscript[\[Zeta], #2], Background -> Purple, LabelStyle -> White]& @@@ ({Subscript[F^\[Degree], pt], Range @ Length @ Subscript[(F^\[Degree]), pt]}\[Transpose]),
        Callout[#1, Subscript[v, #2], CalloutMarker -> "Circle", Background -> Blue, LabelStyle -> White]& @@@ ({Subscript[F, pt], Range @ Length @ Subscript[F, pt]}\[Transpose])
    ]]
  }, PlotRange -> All, Axes -> False, styles]
LabeledPolarHullPlot[F_, superScript_String, transform_, styles___Rule] := Show[{
    PolarHullPlot[F],
    ListPlot[Join[
        Callout[transform @ #1, Subscript[\[Zeta], #2]^superScript, Background -> Purple, LabelStyle -> Directive[Medium, Bold, White]]& @@@ ({Subscript[F^\[Degree], pt], Range @ Length @ Subscript[(F^\[Degree]), pt]}\[Transpose]),
        Callout[transform @ #1, Subscript[v, #2]^superScript, Background -> Blue, LabelStyle -> Directive[Medium, Bold, White]]& @@@ ({Subscript[F, pt], Range @ Length @ Subscript[F, pt]}\[Transpose])
      ], PlotStyle -> Transparent]
  }, PlotRange -> All, Axes -> False, styles]

PolarPlot0[F_, styles___Rule] := Graphics[{
    Blue, Thick, Line[{#1, #2}]& @@@ rotatedPairs[Subscript[F^\[Degree], pt]],
    Purple, Arrow[{{0, 0}, #}]& /@ (Subscript[F^\[Degree], pt]),
    Gray, Thin, Dashed, Circle[]
  }, styles]
LabeledPolarPlot[F_, superScript_String, transform_, styles___Rule] := Show[{
    Graphics[{
        Blue, Thick, Line[transform /@ {#1, #2}]& @@@ rotatedPairs[Subscript[F^\[Degree], pt]],
        Purple, Arrow[transform /@ {{0, 0}, #}]& /@ (Subscript[F^\[Degree], pt]),
        Gray, Thin, Dashed, Circle[]
      }, styles],
    ListPlot[Join[
        Callout[transform @ #1, Subscript[\[Zeta], #2]^superScript, Background -> Purple, LabelStyle -> Directive[Medium, Bold, White]]& @@@ ({Subscript[F^\[Degree], pt], Range @ Length @ Subscript[(F^\[Degree]), pt]}\[Transpose])
      ], PlotStyle -> Transparent]
  }, PlotRange -> All, Axes -> False, styles]