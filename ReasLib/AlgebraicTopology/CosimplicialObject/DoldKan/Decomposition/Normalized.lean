/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import ReasLib.AlgebraicTopology.CosimplicialObject.DoldKan.Normalized.Quotient
public import ReasLib.Algebra.Homology.HomologicalComplex.Biproduct
public import Mathlib.CategoryTheory.Limits.FunctorCategory.BinaryBiproducts
public import Mathlib.Algebra.Homology.HomologicalComplexAbelian
public import Mathlib.Tactic.CrossRefAttribute

/-!
@stack 019I

# Source-facing normalized--degenerate decomposition

This leaf owns the source-facing splitting of the alternating coface complex into the explicit
degenerate and normalized cochain complexes.
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits AlgebraicTopology

noncomputable section

universe u v

namespace CategoryTheory.CosimplicialObject

variable {A : Type u} [Category.{v} A]

section Data

variable [Preadditive A] [HasZeroObject Aᵒᵖ] [HasBinaryCoproducts Aᵒᵖ] [HasImages Aᵒᵖ]
  [HasCokernels (CochainComplex A ℕ)] [HasBinaryBiproducts A]

namespace normalizedCochainComplex

/-- The natural comparison from the degenerate--normalized biproduct to the alternating coface
complex. -/
@[stacks 019I "normalized-degenerate comparison"]
def decomposition.toAlternating :
    (degenerateCochainComplex.functor (A := A)) ⊞ normalizedCochainComplex.functor (A := A) ⟶
      alternatingCofaceMapComplex A :=
  biprod.desc degenerateCochainComplex.ι.natTrans ι.natTrans

/-- The natural projection from the alternating coface complex to the degenerate--normalized
biproduct. -/
@[stacks 019I "normalized-degenerate projection"]
def decomposition.fromAlternating :
    alternatingCofaceMapComplex A ⟶
      (degenerateCochainComplex.functor (A := A)) ⊞ normalizedCochainComplex.functor (A := A) :=
  biprod.lift degenerateCochainComplex.ρ.natTrans π.natTrans

/-- The degenerate coordinate of the source-facing comparison. -/
@[reassoc, stacks 019I "degenerate coordinate of the normalized-degenerate comparison"]
theorem decomposition.toAlternating.inl_app (U : CosimplicialObject A) :
    ((biprod.inl : degenerateCochainComplex.functor (A := A) ⟶
        (degenerateCochainComplex.functor (A := A)) ⊞ normalizedCochainComplex.functor (A := A)).app U) ≫
      (decomposition.toAlternating (A := A)).app U = degenerateCochainComplex.ι U := sorry

/-- The normalized coordinate of the source-facing comparison. -/
@[reassoc, stacks 019I "normalized coordinate of the normalized-degenerate comparison"]
theorem decomposition.toAlternating.inr_app (U : CosimplicialObject A) :
    ((biprod.inr : normalizedCochainComplex.functor (A := A) ⟶
        (degenerateCochainComplex.functor (A := A)) ⊞ normalizedCochainComplex.functor (A := A)).app U) ≫
      (decomposition.toAlternating (A := A)).app U = ι U := sorry

/-- The degenerate coordinate of the source-facing projection. -/
@[reassoc, stacks 019I "degenerate coordinate of the normalized-degenerate projection"]
theorem decomposition.fromAlternating.app_fst (U : CosimplicialObject A) :
    (decomposition.fromAlternating (A := A)).app U ≫
      ((biprod.fst :
        (degenerateCochainComplex.functor (A := A)) ⊞ normalizedCochainComplex.functor (A := A) ⟶
          degenerateCochainComplex.functor (A := A)).app U) = degenerateCochainComplex.ρ U := sorry

/-- The normalized coordinate of the source-facing projection. -/
@[reassoc, stacks 019I "normalized coordinate of the normalized-degenerate projection"]
theorem decomposition.fromAlternating.app_snd (U : CosimplicialObject A) :
    (decomposition.fromAlternating (A := A)).app U ≫
      ((biprod.snd :
        (degenerateCochainComplex.functor (A := A)) ⊞ normalizedCochainComplex.functor (A := A) ⟶
          normalizedCochainComplex.functor (A := A)).app U) = π U := sorry

/-- The source-facing comparison followed by projection is the identity. -/
@[stacks 019I "normalized-degenerate comparison inverse law"]
theorem decomposition.to_comp_from :
    decomposition.toAlternating (A := A) ≫ decomposition.fromAlternating (A := A) = 𝟙 _ := sorry

/-- The source-facing projection followed by comparison is the identity. -/
@[stacks 019I "normalized-degenerate comparison inverse law"]
theorem decomposition.from_comp_to :
    decomposition.fromAlternating (A := A) ≫ decomposition.toAlternating (A := A) = 𝟙 _ := sorry

/-- The alternating coface complex splits into source-facing degenerate and normalized cochain
summands. -/
@[stacks 019I "normalized-degenerate decomposition"]
def decomposition :
    (degenerateCochainComplex.functor (A := A)) ⊞ normalizedCochainComplex.functor (A := A) ≅
      alternatingCofaceMapComplex A where
  hom := decomposition.toAlternating (A := A)
  inv := decomposition.fromAlternating (A := A)
  hom_inv_id := decomposition.to_comp_from (A := A)
  inv_hom_id := decomposition.from_comp_to (A := A)

/-- The forward map of the source-facing decomposition. -/
@[simp, stacks 019I "normalized-degenerate decomposition forward map"]
theorem decomposition.hom_eq :
    (decomposition (A := A)).hom = decomposition.toAlternating (A := A) := sorry

/-- The inverse map of the source-facing decomposition. -/
@[simp, stacks 019I "normalized-degenerate decomposition inverse map"]
theorem decomposition.inv_eq :
    (decomposition (A := A)).inv = decomposition.fromAlternating (A := A) := sorry

/-- The source-oriented splitting of the alternating coface complex. -/
@[stacks 019I "source-oriented normalized-degenerate splitting"]
def splitting : alternatingCofaceMapComplex A ≅
    (degenerateCochainComplex.functor (A := A)) ⊞ normalizedCochainComplex.functor (A := A) :=
  (decomposition (A := A)).symm

/-- The forward map of the source-oriented splitting. -/
@[simp, stacks 019I "normalized-degenerate splitting forward map"]
theorem splitting.hom_eq :
    (splitting (A := A)).hom = decomposition.fromAlternating (A := A) := sorry

/-- The inverse map of the source-oriented splitting. -/
@[simp, stacks 019I "normalized-degenerate splitting inverse map"]
theorem splitting.inv_eq :
    (splitting (A := A)).inv = decomposition.toAlternating (A := A) := sorry

/-- The degenerate projection annihilates the normalized inclusion. -/
@[reassoc, stacks 019I "degenerate projection annihilates normalized cochains"]
theorem inclusion_comp_degenerateProjection (U : CosimplicialObject A) :
    ι U ≫ degenerateCochainComplex.ρ U = 0 := sorry

/-- The degenerate and normalized projectors sum to the identity. -/
@[stacks 019I "degenerate-normalized projector decomposition"]
theorem projector_sum (U : CosimplicialObject A) :
    degenerateCochainComplex.ρ U ≫ degenerateCochainComplex.ι U + π U ≫ ι U = 𝟙 _ := sorry

end normalizedCochainComplex

end Data

section QuasiIso

variable [Abelian A]

namespace normalizedCochainComplex

namespace π

/-- The normalized projection is a quasi-isomorphism in an Abelian target. -/
@[stacks 019I "normalized cochain quasi-isomorphism"]
instance quasiIso (U : CosimplicialObject A) : QuasiIso (π U) := sorry

end π

end normalizedCochainComplex

end QuasiIso

end CategoryTheory.CosimplicialObject
