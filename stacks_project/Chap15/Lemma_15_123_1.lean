/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.Algebra.Homology.CochainComplex.Determinant.CanonicalElement
import StacksCheckRecall

/-!
# Determinants and canonical elements of two-term complexes

The determinant line, admissibility predicate, rank-zero predicate, canonical element, and their
functoriality are owned by
`ReasLib.Algebra.Homology.CochainComplex.Determinant.CanonicalElement`.

@stack 0FJJ
-/

@[expose] public section

/- Lemma 15.123.1 (0FJJ): the determinant equivalence of an admissible morphism carries the
canonical element of the source to the canonical element of the target. -/
@[stacks 0FJJ "determinant maps preserve canonical elements"]
#check @CochainComplex.Determinant.equiv_canonical

#check @CochainComplex.Determinant.line
#check @CochainComplex.Determinant.IsAdmissible
#check @CochainComplex.Determinant.kernelDifferential
#check @CochainComplex.Determinant.IsRankZero
#check @CochainComplex.Determinant.canonical
#check @CochainComplex.Determinant.IsRankZero.source
#check @CochainComplex.Determinant.equiv
#check @CochainComplex.Determinant.map
