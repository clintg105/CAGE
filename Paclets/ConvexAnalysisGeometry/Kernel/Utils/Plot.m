(* ::Package:: *)

Package["ConvexAnalysisGeometry`Utils`"]

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