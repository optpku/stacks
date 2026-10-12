/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import ReasLib.CategoryTheory.InverseSystem.MittagLeffler.Homology
import StacksCheckRecall

/-!
# Lemma 12.31.7

The source degree-zero comparison is the `n = 0` specialization of the degree-uniform neutral
API.
-/

open CategoryTheory CategoryTheory.Limits ComplexShape

noncomputable section

/- Lemma 12.31.7: for a sequential inverse system `A` of cochain complexes of abelian groups,
Mittag-Leffler conditions in degrees `-2` and `-1`, together with essential constancy of
`H⁻¹(A)`, make the canonical map `H⁰(lim A) ⟶ lim H⁰(A)` an isomorphism. -/
@[stacks 070E] #check
  (fun (A : SequentialInverseSystem (CochainComplex AddCommGrpCat ℤ))
      (hneg₂ : SequentialInverseSystem.IsMittagLeffler
        (A ⋙ HomologicalComplex.eval AddCommGrpCat (up ℤ) ((0 : ℤ) - 2)))
      (hneg₁ : SequentialInverseSystem.IsMittagLeffler
        (A ⋙ HomologicalComplex.eval AddCommGrpCat (up ℤ) ((0 : ℤ) - 1)))
      (hHneg₁ : IsCofiltered.IsEssentiallyConstant
        (A ⋙ HomologicalComplex.homologyFunctor AddCommGrpCat (up ℤ) ((0 : ℤ) - 1))) ↦
    CategoryTheory.SequentialInverseSystem.LimitHomology.isIso
      A 0 hneg₂ hneg₁ hHneg₁)
