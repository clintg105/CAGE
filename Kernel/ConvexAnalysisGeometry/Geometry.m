(* ::Package:: *)

Package["ConvexAnalysisGeometry`"]
PackageImport["ConvexAnalysisGeometry`Utils`"]

PackageExport["GetAffineHullDim"]


GetAffineHullDim::usage = "GetAffineHullDim[pts_List] returns the \
dimension of the affine hull spanned by `pts`"
(* The rank of the (centered) point matrix is the dimension of the \
affine subspace spanned by the points*)
GetAffineHullDim[pts_List] := MatrixRank[addRow[pts[[2 ;;]], -pts[[1]]]]