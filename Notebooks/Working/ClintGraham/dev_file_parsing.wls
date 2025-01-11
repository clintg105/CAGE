#!/usr/bin/env wolframscript
(* ::Package:: *)

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
          StringCases[line, (" :> "|" := "|" /; "|" && "|" || ") ~~ Whitespace... ~~ EndOfLine],
          WhitespaceCharacter -> ""];
        newLine = StringRepeat["  ", Max[0, cumulativeBalance-leadingCloseCount+Length @ hangingOperatorMat]]<>line<>"\n";
        Echo[{newLine,hangingOperators,hangingOperatorMat}];
        (* Note: only works on single-line comments and strings *)
        cumulativeBalance += StringCount[#, "("|"{"|"["]-StringCount[#, ")"|"}"|"]"]& @ RemoveCommentsAndStrings[line];
        (* if something goes horribly wrong we don't want to "dig a hole" *)
        cumulativeBalance = Max[0, cumulativeBalance];
        hangingOperatorMat = Select[hangingOperatorMat, # < cumulativeBalance+Length[hangingOperators]&];
        If[Length[hangingOperators]>0, AppendTo[hangingOperatorMat, cumulativeBalance]];
        newLine
      ], lines]
  ];
  StringTrim[result, "\n"]
]


IndentStringByBraces@"showDiscreteColorThemes[] :=
Grid[{#, getDiscreteColorTheme[#]} & /@ (\"Color\" /.
    Charting`$PlotThemes), Dividers -> All]
getDiscreteColorTheme[name_] :=
Cases[\"DefaultPlotStyle\" /. (Method /.
    Charting`ResolvePlotTheme[name, ListPlot]), _RGBColor, Infinity]"



