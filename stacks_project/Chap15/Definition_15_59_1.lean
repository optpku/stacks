/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import ReasLib.Algebra.Homology.CochainComplex.KFlat
import StacksCheckRecall

/-!
# Definition 15.59.1

@stack 06XZ

The reusable K-flatness API is owned by
`ReasLib.Algebra.Homology.CochainComplex.KFlat`.
-/

@[expose] public section

/- Definition 15.59.1, tag `06XZ`: K-flat cochain complexes. -/
@[stacks 06XZ "K-flat cochain complex"]
#check @CochainComplex.IsKFlat
