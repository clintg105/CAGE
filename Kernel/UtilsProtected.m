(* ::Package:: *)

Package["ConvexAnalysisGeometry`Utils`"]

(* ::Section:: *)
(*Development*)
PackageExport["$ConvexAnalysisGeometryDir"]
PackageExport["RemoveCommentsAndStrings"]
PackageExport["IndentStringByBraces"]
PackageExport["SpaceOperators"]
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
          StringCases[line, (":>"|":="|"/;"|"&&"|"||")~~Whitespace...~~EndOfLine],
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
      (w...~~"==="~~w...) :> " === "
      , (w...~~"=="~~w...) :> " == "
      , (w...~~"=>"~~w...) :> " => " (* mostly used in comments *)
      , (w...~~"!="~~w...) :> " != "
      , (w...~~"=!="~~w...) :> " =!= "
      , (w...~~"="~~w...) :> " = "
      , (","~~w...) :> ", "
      , (w...~~":="~~w...) :> " := "
      , (w...~~"^:="~~w...) :> " ^:= "
      , (w...~~"+="~~w...) :> " += "
      , (w...~~"-="~~w...) :> " -= "
      , (w...~~">="~~w...) :> " >= "
      , (w...~~"<="~~w...) :> " <= "
      , (w...~~"&&"~~w...) :> " && "
      , (w...~~"||"~~w...) :> " || "
      , (w...~~"->"~~w...) :> " -> "
      , (w...~~"|->"~~w...) :> " |-> "
      , (w...~~":>"~~w...) :> " :> "
      , (w...~~"/."~~w...) :> " /. "
      , (w...~~"//."~~w...) :> " //. "
      , (w...~~"/;"~~w...) :> " /; "
      , (w...~~"/@"~~w...) :> " /@ "
      , (w...~~"//@"~~w...) :> " //@ "
      , (w...~~"@@@"~~w...) :> " @@@ "
      , (w...~~"@@"~~w...) :> " @@ "
      , (w...~~"@"~~w...) :> " @ "
}]]

CAGHelper[]:=CreatePalette[Block[{sep},DynamicModule[
      {nbOld,nbNew,hasDevAssoc},
      Dynamic[Refresh[
          hasDevAssoc:=FileSystemMap[
            sep[#,FileExistsQ@FileNameJoin[{FileNameDrop[#],FileBaseName[#]<>"_dev-nb.nb"}]]&,
            FileNameJoin[{$ConvexAnalysisGeometryDir,"Kernel"}],
            Infinity,
            FileNameForms->RegularExpression[".*(?!Protected)\\.(wl|m)"]
          ] //. x_Association :> KeyDrop[x,
            Select[Keys @ x, StringContainsQ[#, "Protected"]&]];
          Column[{(
                hasDevAssoc/.Association->List//.Rule[k_,v_List]:>OpenerView[{k,v//Column},False]//Column
                )/.{
                Rule[k_,sep[v_,False]]:>Button[k,
                  With[{devNB=StringReplace[v, RegularExpression["\\.(wl|m)$"] -> "_dev-nb.nb"]},
                    Export[v,StringTrim[#,Whitespace]&/@Import[v,"Lines"],"Lines"];
                    nbOld=NotebookOpen[v, Visible -> False];
                    FrontEndTokenExecute[nbOld,"SaveRename",{devNB,"Notebook"}];
                    NotebookClose[nbOld];
                    Export[v,SpaceOperators@IndentStringByBraces[Import[v,"Text"]],"Text"];
                    Export[devNB,StringReplace[Import[devNB,"Text"],"\"\\n\", "->"\"\\[IndentingNewLine]\", "],"Text"];

                    nbNew=NotebookOpen[devNB, Visible -> True];
                    SetOptions[nbNew,
                      NotebookEventActions->{
                        {"MenuCommand","Save"}:>With[{pkgName=StringReplace[NotebookFileName[],"_dev-nb.nb"->"."<>FileExtension[v]]},
                          FrontEndTokenExecute[FrontEnd`InputNotebook[],"SaveRename",{pkgName,"Package"}];
                          Export[pkgName,SpaceOperators@IndentStringByBraces[Import[pkgName,"Text"]],"Text"];
                        ],
                        PassEventsDown->True},
                      PrivateNotebookOptions -> {"FileOutlineCache" -> None}];
                    FrontEndExecute[NotebookWrite[#,Replace[NotebookRead[#],"Code"->Sequence["Input","InitializationCell"->True],All]]&/@Cells[nbNew,CellStyle->"Code"]];
                    NotebookSave[nbNew];
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
                ]],
              Button["Quit & Close",
                nbOld={};
                (*FrontEndExecute[
                  Quit[];
                  PacletDirectoryLoad[$ConvexAnalysisGeometryDir];
                  Needs["ConvexAnalysisGeometry`"]
                ]*)
                NotebookClose[Cases[If[Options[#, WindowTitle] == {WindowTitle -> "CAG Dev Helper"}, #, Null] & /@ Notebooks[], _NotebookObject][[1]]];
                Quit[];
              ]
          }],
          TrackedSymbols:>{nbOld},UpdateInterval->1]]
  ]],WindowTitle->"CAG Dev Helper",Saveable -> False]