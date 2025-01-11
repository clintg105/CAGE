(* ::Package:: *)

Package["ConvexAnalysisGeometry`Utils`"]

(* ::Section:: *)
(*Geometry*)


(* ::Input::Initialization:: *)
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


(* ::Input::Initialization:: *)
trep[expr_, vars_, inp_] := expr /. Thread[vars -> inp]
mtrep[expr_, vars_, inp_] := expr /. Thread[vars -> #] & /@ inp

repelem[ix_List] :=
Flatten[ConstantArray[#1, #2] & @@@ Transpose @ {Range[Length[ix]], ix}]
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
  cnds = Append[cnds, Not @ Fold[Or, cnds]];
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


(* ::Section:: *)
(*Combinatorics*)


(* ::Input::Initialization:: *)
PackageExport["NthKSubset"]
PackageExport["NextKSubset"]
PackageExport["FirstKSubsetIx"]
PackageExport["FirstKSubset"]


(* ::Input::Initialization:: *)
NthKSubset::usage =
"NthKSubset[n, k, N] computes the n-th k-subset of a set of size N \
in lexicographical order.
Complexity: O(k log N) time, O(k) space.
Efficient for direct access to the n-th subset without generating \
preceding subsets. Ideal for large n or sparse indexing.";
(*Efficient computation of the n-th k-subset: NthKSubset[5, 3, 5] > \
  {1, 4, 5}*)
NthKSubset[n_Integer?NonNegative, k_Integer?Positive,
  m_Integer?Positive] /; Binomial[m, k] > n := Block[
  {subset, r = n, x = 1, remaining = k},
  Reap[
    While[remaining > 0 && x <= m,
      If[Binomial[m - x, remaining - 1] > r,
        Sow[x]; remaining -= 1; x += 1,
        r -= Binomial[m - x, remaining - 1]; x += 1
      ]
    ]
  ][[2, 1]]]


(* ::Input::Initialization:: *)
NextKSubset::usage =
"NextKSubset[current, N] computes the next k-subset in \
lexicographical order from the given subset `current`.
Complexity: O(k) time, O(k) space.
Optimal for sequential subset traversal or stepwise generation when \
the current subset is known.
Note: The first k-subset is simply Range[k].";
(*Function to compute the next k-subset in lex order: \
  NextKSubset[{2, 3, 4}, 5] > {2, 3, 5}; NextKSubset[{4, 5}, 5] > {}*)
NextKSubset[current_List, m_Integer?Positive] /;
OrderedQ[current] && Max[current] <= m := With[
  {k = Length[current]},
  Block[
    {i = k, subset = current},
    (*Find the rightmost element that can be incremented*)
    While[i > 0 && subset[[i]] == m - k + i, i--];
    If[i == 0,
      (*No next subset exists*){},
      subset[[i]] += 1;
      subset = ReplacePart[subset,
        Thread[
          Range[i + 1, k] -> Range[subset[[i]] + 1, subset[[i]] + k - i]]
      ];
      subset
    ]
  ]
]


FirstKSubsetIx[set_, k_, test_] := NestWhile[
  NextKSubset[#, Length[set]] &,
  Range[k],
  ! test[set[[#]]] &,
  1, Binomial[Length[set], k]
]
FirstKSubset[set_, k_, test_] := set[[FirstKSubsetIx[set, k, test]]]


(* ::Section:: *)
(*Plots*)


(* ::Input::Initialization:: *)
PackageExport["showDiscreteColorThemes"]
PackageExport["getDiscreteColorTheme"]

(* https://mathematica.stackexchange.com/questions/54486/how-to-\
  access-new-colour-schemes-in-version-10 *)
showDiscreteColorThemes[] :=
Grid[{#, getDiscreteColorTheme[#]} & /@ ("Color" /.
    Charting`$PlotThemes), Dividers -> All]
getDiscreteColorTheme[name_] :=
Cases["DefaultPlotStyle" /. (Method /.
    Charting`ResolvePlotTheme[name, ListPlot]), _RGBColor, Infinity]


(* ::Section:: *)
(*Development*)
PackageExport["$ConvexAnalysisGeometryDir"]
PackageExport["RemoveCommentsAndStrings"]
PackageExport["IndentStringByBraces"]
PackageExport["CAGHelper"]

$ConvexAnalysisGeometryDir = ParentDirectory[DirectoryName[$InputFileName]];

RemoveCommentsAndStrings[line_String] := StringReplace[line, {
    RegularExpression["\\(\\*.*?\\*\\)"] -> "", (*Remove comments*)
    RegularExpression["\"(\\\\.|[^\"])*\""] -> "" (*Remove strings*)
}];
IndentStringByBraces[str_String] := Module[
  {lines, result, leadingCloseCount, newLine,
    cumulativeBalance = 0, hangingOperators, hangingOperatorMat = {}},
  lines = StringSplit[str, "\n"];
  result = StringJoin[
    Map[Function[line,
        leadingCloseCount = StringLength @ StringReplace[
          StringCases[line, RegularExpression["^ *(\)|\]|\})*"]],
          WhitespaceCharacter -> ""][[1]];
        hangingOperators = StringReplace[
          StringCases[line, (" :> "|" := "|" /; "|" && "|" || ")~~Whitespace...~~EndOfLine],
          WhitespaceCharacter -> ""];
        newLine = StringRepeat["  ", Max[0, cumulativeBalance-leadingCloseCount+Length @ hangingOperatorMat]]<>line<>"\n";
        (* Note: only works on single-line comments and strings *)
        cumulativeBalance += StringCount[#, "("|"{"|"["]-StringCount[#, ")"|"}"|"]"]& @ RemoveCommentsAndStrings[line];
        (* if something goes horribly wrong we don't want to "dig a hole" *)
        cumulativeBalance = Max[0, cumulativeBalance];
        hangingOperatorMat = Select[hangingOperatorMat, #<cumulativeBalance+Length[hangingOperators]&];
        If[Length[hangingOperators]>0, AppendTo[hangingOperatorMat, cumulativeBalance]];
        newLine
      ], lines]
  ];
  StringTrim[result, "\n"]
]
SpaceOperators[string_] := StringReplace[string, With[{w = " "|"\t"}, {
      (w...~~" === "~~w...) :> " === "
      , (w...~~" == "~~w...) :> " == "
      , (w...~~" => "~~w...) :> " => " (* mostly used in comments *)
      , (w...~~" != "~~w...) :> " != "
      , (w...~~" =!= "~~w...) :> " =!= "
      , (w...~~" = "~~w...) :> " = "
      , (w...~~" := "~~w...) :> " := "
      , (w...~~" ^:= "~~w...) :> " ^:= "
      , (w...~~" += "~~w...) :> " += "
      , (w...~~" -= "~~w...) :> " -= "
      , (w...~~" >= "~~w...) :> " >= "
      , (w...~~" <= "~~w...) :> " <= "
      , (w...~~" && "~~w...) :> " && "
      , (w...~~" || "~~w...) :> " || "
      , (w...~~" -> "~~w...) :> " -> "
      , (w...~~" |-> "~~w...) :> " |-> "
      , (w...~~" :> "~~w...) :> " :> "
      , (w...~~" /. "~~w...) :> " /. "
      , (w...~~" //. "~~w...) :> " //. "
      , (w...~~" /; "~~w...) :> " /; "
      , (w...~~" /@ "~~w...) :> " /@ "
      , (w...~~" //@ "~~w...) :> " //@ "
      , (w...~~" @@@ "~~w...) :> " @@@ "
      , (w...~~" @@ "~~w...) :> " @@ "
      , (w...~~" @ "~~w...) :> " @ "
      , (", "~~w...) :> ", "
}]]

CAGHelper[]:=CreatePalette[Block[{sep},DynamicModule[
      {nbOld,nbNew,hasDevAssoc},
      Dynamic[Refresh[
          hasDevAssoc:=FileSystemMap[
            sep[#,FileExistsQ@FileNameJoin[{FileNameDrop[#],FileBaseName[#]<>"_dev-nb.nb"}]]&,
            FileNameJoin[{$ConvexAnalysisGeometryDir,"Kernel"}],
            Infinity,
            FileNameForms->RegularExpression[".*\\.(wl|m)"]
          ];
          Column[{(
                hasDevAssoc/.Association->List//.Rule[k_,v_List]:>OpenerView[{k,v//Column},True]//Column
                )/.{
                Rule[k_,sep[v_,False]]:>Button[k,
                  With[{devNB=StringReplace[v, RegularExpression["\\.(wl|m)$"] -> "_dev-nb.nb"]},
                    Export[v,StringTrim[#,Whitespace]&/@Import[v,"Lines"],"Lines"];
                    nbOld=NotebookOpen[v];
                    FrontEndTokenExecute[nbOld,"SaveRename",{devNB,"Notebook"}];
                    NotebookClose[nbOld];
                    Export[v,SpaceOperators@IndentStringByBraces[Import[v,"Text"]],"Text"];
                    Export[devNB,StringReplace[Import[devNB,"Text"],"\"\\n\", "->"\"\\[IndentingNewLine]\", "],"Text"];
                    nbNew=NotebookOpen[devNB];
                    SetOptions[nbNew,
                      NotebookEventActions->{
                        {"MenuCommand","Save"}:>With[{pkgName=StringReplace[NotebookFileName[],"_dev-nb.nb"->"."<>FileExtension[v]]},
                          FrontEndTokenExecute[FrontEnd`InputNotebook[],"SaveRename",{pkgName,"Package"}];
                          Export[pkgName,SpaceOperators@IndentStringByBraces[Import[pkgName,"Text"]],"Text"];
                        ],
                        PassEventsDown->True}];
                    FrontEndExecute[NotebookWrite[#,Replace[NotebookRead[#],"Code"->Sequence["Input","InitializationCell"->True],All]]&/@Cells[nbNew,CellStyle->"Code"]]
                  ],Alignment->Left,Background->Lighter[Gray, 0.9]],
                Rule[k_,sep[v_,True]]:>Button[k,
                  With[{devNB=StringReplace[v, RegularExpression["\\.(wl|m)$"] -> "_dev-nb.nb"]},
                    NotebookOpen[devNB]
                  ],Alignment->Left,Background->LightBlue]
              },
              Button["Delete All Dev Notebooks",
                nbOld={};
                FileSystemMap[
                  Check[DeleteFile@#,NotebookOpen@#]&,
                  FileNameJoin[{$ConvexAnalysisGeometryDir,"Kernel"}],
                  Infinity,
                  FileNameForms->"*_dev-nb.nb"
                ]
          ]}],
          TrackedSymbols:>{nbOld},UpdateInterval->1]]
  ]],WindowTitle->"CAG Dev Helper"]