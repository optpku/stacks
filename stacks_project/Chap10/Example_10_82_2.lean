/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.Algebra.Homology.ShortComplex.UniversallyExact.Colimit
import StacksCheckRecall

@[expose] public section

/-!
# Example 10.82.2

@stack 058J
-/

/-!
# Filtered colimits of universally exact complexes

Example 10.82.2 is recalled from the neutral universal-exactness colimit API.
The main reusable statement is tagged `058J` on
`CategoryTheory.ShortComplex.UniversallyExact.colimit_of_isFiltered`.
-/

@[stacks 058J "split complex"]
#check CategoryTheory.ShortComplex.Splitting.universallyExact
@[stacks 058J "tensor exactness"]
#check CategoryTheory.ShortComplex.UniversallyExact.tensorLeft_shortExact
@[stacks 058J "filtered colimit"]
#check CategoryTheory.ShortComplex.UniversallyExact.colimit_of_isFiltered
@[stacks 058J "colimit of split complexes"]
#check CategoryTheory.ShortComplex.UniversallyExact.colimit_of_split
