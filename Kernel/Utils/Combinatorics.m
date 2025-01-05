(* ::Package:: *)

Package["ConvexAnalysisGeometry`Utils`"]

PackageExport["NthKSubset"]
PackageExport["NextKSubset"]
PackageExport["FirstKSubsetIx"]
PackageExport["FirstKSubset"]


NthKSubset::usage = 
  "NthKSubset[n, k, N] computes the n-th k-subset of a set of size N \
in lexicographical order.
Complexity: O(k log N) time, O(k) space. 
Efficient for direct access to the n-th subset without generating \
preceding subsets. Ideal for large n or sparse indexing.";
(*Efficient computation of the n-th k-subset: NthKSubset[5,3,5] > \
{1,4,5}*)
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


NextKSubset::usage = 
  "NextKSubset[current, N] computes the next k-subset in \
lexicographical order from the given subset `current`. 
Complexity: O(k) time, O(k) space. 
Optimal for sequential subset traversal or stepwise generation when \
the current subset is known.
Note: The first k-subset is simply Range[k].";
(*Function to compute the next k-subset in lex order: \
NextKSubset[{2,3,4},5] > {2,3,5}; NextKSubset[{4,5},5] > {}*)
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