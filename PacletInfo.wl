(* ::Package:: *)

PacletObject[
  <|
    "Name" -> "ConvexAnalysisGeometry",
    "Description" -> "Convex Analysis Toolkit",
    "Creator" -> "Clinten Graham",
    "License" -> "MIT",
    "Version" -> "0.1",
    "WolframVersion" -> "13.0+",
    "Extensions" -> {
		
        (* Kernel Extension for the Core Package *)
        {
            "Kernel", 
            "Root" -> "Kernel", 
            "Context" -> {"ConvexAnalysisGeometry`", "ConvexAnalysisGeometry`Utils`"}
        },
        
        (* Documentation Extension *)
        {
            "Documentation",
            "Language" -> "English",
            "MainPage" -> "Guides/ConvexAnalysisGeometry",
            "LinkBase" -> "ConvexAnalysisGeometry"
        },
        
        (* Asset Extension for Additional Resources *)
        {
            "Asset", 
            "Root" -> "Assets", 
            "Assets" -> {"Images", "Styles", "OtherResources"}
        }
    }
  |>
]
