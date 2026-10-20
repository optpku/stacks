/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import Mathlib.Algebra.Category.Grp.AB
public import ReasLib.CategoryTheory.Homology.DoubleComplex.AugmentedResolution
import StacksCheckRecall

/-!
# Lemma 12.26.4

Source-facing checks for product totalization of an augmented resolution.  The product total
and its symmetric zeroth-row and zeroth-column comparisons are owned by
`HomologicalComplex₂.ProductTotal`. The exact-resolution theorem for abelian groups is owned by
`HomologicalComplex₂.AugmentedResolution` in `ReasLib`.
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits ComplexShape HomologicalComplex

noncomputable section

universe v u

variable {C : Type u} [Category.{v} C] [Preadditive C] [HasZeroObject C]
  [HasCountableProducts C]
variable {K : CochainComplex C ℤ}
variable {A : HomologicalComplex₂ C (up ℤ) (up ℤ)}
variable (fRow : A.zeroRow ⟶ K) (hfRow : A.flip.d (-1) 0 ≫ fRow = 0)
variable (fColumn : A.zeroColumn ⟶ K) (hfColumn : A.d (-1) 0 ≫ fColumn = 0)

/- The product total is a functorial construction obtained from the canonical coproduct total in
the opposite category. -/
#check (HomologicalComplex₂.ProductTotal.complex A : CochainComplex C ℤ)
#check (HomologicalComplex₂.ProductTotal.functor (C := C) :
  HomologicalComplex₂ C (up ℤ) (up ℤ) ⥤ CochainComplex C ℤ)

/- The generic product-total projections to a zeroth row or zeroth column require precisely the
corresponding incoming-differential condition. -/
#check (HomologicalComplex₂.ProductTotal.ZeroRow.FromTotal.map fRow hfRow :
  HomologicalComplex₂.ProductTotal.complex A ⟶ K)
#check (HomologicalComplex₂.ProductTotal.ZeroColumn.FromTotal.map fColumn hfColumn :
  HomologicalComplex₂.ProductTotal.complex A ⟶ K)
#check (HomologicalComplex₂.ProductTotal.ZeroRow.FromTotal.map_op fRow hfRow :
  (HomologicalComplex₂.ProductTotal.ZeroRow.FromTotal.map fRow hfRow).op =
    (CochainComplex.opEquivalence C).unitIso.hom.app (Opposite.op K) ≫
      (CochainComplex.opEquivalence C).inverse.map
        (HomologicalComplex₂.ProductTotal.ZeroRow.FromTotal.op fRow hfRow))
#check (HomologicalComplex₂.ProductTotal.ZeroColumn.FromTotal.map_op fColumn hfColumn :
  (HomologicalComplex₂.ProductTotal.ZeroColumn.FromTotal.map fColumn hfColumn).op =
    (CochainComplex.opEquivalence C).unitIso.hom.app (Opposite.op K) ≫
      (CochainComplex.opEquivalence C).inverse.map
        (HomologicalComplex₂.ProductTotal.ZeroColumn.FromTotal.op fColumn hfColumn))

/- The augmentation specialization keeps `A.d 1 0 ≫ augmentation = 0` explicit. -/
variable {M : CochainComplex C ℤ}
variable (R : ChainComplex (CochainComplex C ℤ) ℕ)
variable (augmentation : R.X 0 ⟶ M) (hAugmentation : R.d 1 0 ≫ augmentation = 0)

#check (HomologicalComplex₂.AugmentedResolution.FromProductTotal.map
  R augmentation hAugmentation :
  HomologicalComplex₂.ProductTotal.complex
    (HomologicalComplex₂.AugmentedResolution.bicomplex R) ⟶ M)

section

variable {N : CochainComplex AddCommGrpCat ℤ}
variable (B : ChainComplex (CochainComplex AddCommGrpCat ℤ) ℕ)
variable (ε : B.X 0 ⟶ N) (hε : B.d 1 0 ≫ ε = 0)
variable [Epi ε]
variable
  (hExactZero : (HomologicalComplex₂.AugmentedResolution.shortComplex B ε hε).Exact)
  (hExact : ∀ n : ℕ, B.ExactAt (n + 1))

/- Lemma 12.26.4 [0E1R]: an exact augmented resolution of complexes of abelian groups maps
quasi-isomorphically from its product total to the augmentation target. -/
@[stacks 0E1R]
#check (HomologicalComplex₂.AugmentedResolution.FromProductTotal.quasiIso_of_exact
  B ε hε hExactZero hExact :
  QuasiIso (HomologicalComplex₂.AugmentedResolution.FromProductTotal.map B ε hε))

end
