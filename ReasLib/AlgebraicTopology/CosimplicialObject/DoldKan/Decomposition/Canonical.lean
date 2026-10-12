/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import ReasLib.AlgebraicTopology.CosimplicialObject.DoldKan.QImage.Normalized
public import ReasLib.AlgebraicTopology.CosimplicialObject.DoldKan.QImage.Split
public import ReasLib.Algebra.Homology.HomologicalComplex.Biproduct
public import Mathlib.Algebra.Homology.HomologicalComplexAbelian
public import Mathlib.CategoryTheory.Limits.FunctorCategory.BinaryBiproducts
public import Mathlib.Tactic.CrossRefAttribute

/-!
# Canonical Dold--Kan normalized--degenerate decomposition

This leaf packages the canonical Dold--Kan degenerate and normalized functors into the alternating
coface complex and records their projector identities.

@stack 019I
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits AlgebraicTopology

noncomputable section

universe u v

namespace CategoryTheory.CosimplicialObject

variable {A : Type u} [Category.{v} A]

section Data

variable [Preadditive A]
  [hI : HasImages (ChainComplex Aᵒᵖ ℕ)]
  [hE : HasStrongEpiImages (ChainComplex Aᵒᵖ ℕ)]
  [hM : HasImageMaps (ChainComplex Aᵒᵖ ℕ)]
  [hC : HasCokernels (CochainComplex A ℕ)]
  [HasBinaryBiproducts A]

include hI hE hM hC

namespace DoldKan.degenerate.decomposition

/-- The canonical comparison from degenerate and normalized summands. -/
@[stacks 019I "canonical degenerate-normalized comparison"]
def toAlternating :
    (DoldKan.degenerate.functor (A := A)) ⊞ DoldKan.degenerate.normalized.functor (A := A) ⟶
      alternatingCofaceMapComplex A :=
  biprod.desc DoldKan.degenerate.ι.natTrans DoldKan.degenerate.normalized.ι.natTrans

/-- The canonical projection onto the two Dold--Kan summands. -/
@[stacks 019I "canonical degenerate-normalized projection"]
def fromAlternating :
    alternatingCofaceMapComplex A ⟶
      (DoldKan.degenerate.functor (A := A)) ⊞ DoldKan.degenerate.normalized.functor (A := A) :=
  biprod.lift DoldKan.degenerate.ρ.natTrans DoldKan.degenerate.normalized.π.natTrans

/-- The degenerate coordinate of the canonical comparison. -/
@[reassoc, stacks 019I "canonical degenerate coordinate formula"]
theorem toAlternating.inl_app (U : CosimplicialObject A) :
    ((biprod.inl : DoldKan.degenerate.functor (A := A) ⟶
        (DoldKan.degenerate.functor (A := A)) ⊞ DoldKan.degenerate.normalized.functor (A := A)).app U) ≫
      (toAlternating (A := A)).app U = DoldKan.degenerate.ι U := sorry

/-- The normalized coordinate of the canonical comparison. -/
@[reassoc, stacks 019I "canonical normalized coordinate formula"]
theorem toAlternating.inr_app (U : CosimplicialObject A) :
    ((biprod.inr : DoldKan.degenerate.normalized.functor (A := A) ⟶
        (DoldKan.degenerate.functor (A := A)) ⊞ DoldKan.degenerate.normalized.functor (A := A)).app U) ≫
      (toAlternating (A := A)).app U = DoldKan.degenerate.normalized.ι U := sorry

/-- The degenerate coordinate of the canonical projection. -/
@[reassoc, stacks 019I "canonical degenerate projection coordinate formula"]
theorem fromAlternating.app_fst (U : CosimplicialObject A) :
    (fromAlternating (A := A)).app U ≫
      ((biprod.fst : (DoldKan.degenerate.functor (A := A)) ⊞
          DoldKan.degenerate.normalized.functor (A := A) ⟶ DoldKan.degenerate.functor (A := A)).app U) =
      DoldKan.degenerate.ρ U := sorry

/-- The normalized coordinate of the canonical projection. -/
@[reassoc, stacks 019I "canonical normalized projection coordinate formula"]
theorem fromAlternating.app_snd (U : CosimplicialObject A) :
    (fromAlternating (A := A)).app U ≫
      ((biprod.snd : (DoldKan.degenerate.functor (A := A)) ⊞
          DoldKan.degenerate.normalized.functor (A := A) ⟶ DoldKan.degenerate.normalized.functor (A := A)).app U) =
      DoldKan.degenerate.normalized.π U := sorry

/-- The canonical comparison followed by projection is the identity. -/
@[stacks 019I "canonical degenerate-normalized comparison inverse law"]
theorem to_comp_from : toAlternating (A := A) ≫ fromAlternating (A := A) = 𝟙 _ := sorry

/-- The canonical projection followed by comparison is the identity. -/
@[stacks 019I "canonical degenerate-normalized projection inverse law"]
theorem from_comp_to : fromAlternating (A := A) ≫ toAlternating (A := A) = 𝟙 _ := sorry

/-- The canonical Dold--Kan decomposition is an isomorphism. -/
@[stacks 019I "canonical degenerate-normalized decomposition"]
def iso :
    (DoldKan.degenerate.functor (A := A)) ⊞ DoldKan.degenerate.normalized.functor (A := A) ≅
      alternatingCofaceMapComplex A where
  hom := toAlternating (A := A)
  inv := fromAlternating (A := A)
  hom_inv_id := to_comp_from (A := A)
  inv_hom_id := from_comp_to (A := A)

/-- The forward map of the canonical decomposition. -/
@[simp, stacks 019I "canonical degenerate-normalized decomposition forward map"]
theorem iso.hom_eq : (iso (A := A)).hom = toAlternating (A := A) := sorry

/-- The inverse map of the canonical decomposition. -/
@[simp, stacks 019I "canonical degenerate-normalized decomposition inverse map"]
theorem iso.inv_eq : (iso (A := A)).inv = fromAlternating (A := A) := sorry

/-- The source-oriented form of the canonical decomposition. -/
@[stacks 019I "source-oriented canonical degenerate-normalized splitting"]
def splitting : alternatingCofaceMapComplex A ≅
    (DoldKan.degenerate.functor (A := A)) ⊞ DoldKan.degenerate.normalized.functor (A := A) :=
  (iso (A := A)).symm

/-- The forward map of the canonical splitting. -/
@[simp, stacks 019I "canonical splitting forward map"]
theorem splitting.hom_eq : (splitting (A := A)).hom = fromAlternating (A := A) := sorry

/-- The inverse map of the canonical splitting. -/
@[simp, stacks 019I "canonical splitting inverse map"]
theorem splitting.inv_eq : (splitting (A := A)).inv = toAlternating (A := A) := sorry

namespace normalized

/-- The canonical degenerate projection annihilates the normalized image. -/
@[reassoc, stacks 019I "canonical degenerate projection annihilates normalized image"]
theorem inclusion_comp_projection (U : CosimplicialObject A) :
    DoldKan.degenerate.normalized.ι (A := A) U ≫ DoldKan.degenerate.ρ (A := A) U = 0 := sorry

end normalized

/-- The canonical degenerate and normalized projectors sum to the identity. -/
@[stacks 019I "canonical degenerate-normalized projector decomposition"]
theorem projector_sum (U : CosimplicialObject A) :
    DoldKan.degenerate.ρ (A := A) U ≫ DoldKan.degenerate.ι (A := A) U +
        DoldKan.degenerate.normalized.π (A := A) U ≫ DoldKan.degenerate.normalized.ι (A := A) U =
      𝟙 ((alternatingCofaceMapComplex A).obj U) := sorry

end DoldKan.degenerate.decomposition

end Data

section QuasiIso

variable [Abelian A]

namespace DoldKan.degenerate.normalized.π

/-- The canonical normalized quotient is a quasi-isomorphism in an Abelian target. -/
@[stacks 019I "canonical normalized quotient quasi-isomorphism"]
instance quasiIso (U : CosimplicialObject A) :
    QuasiIso (DoldKan.degenerate.normalized.π (A := A) U) := sorry

end DoldKan.degenerate.normalized.π

end QuasiIso

end CategoryTheory.CosimplicialObject
