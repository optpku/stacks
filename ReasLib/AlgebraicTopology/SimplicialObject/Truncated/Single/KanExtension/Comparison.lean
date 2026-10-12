/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import ReasLib.AlgebraicTopology.SimplicialObject.Truncated.Single.KanExtension.Skeleton.Biproduct
public import ReasLib.AlgebraicTopology.SimplicialObject.Truncated.Single.KanExtension.Coskeleton.Biproduct
public import ReasLib.AlgebraicTopology.SimplicialObject.Truncated.Adjunction

/-!
@stack 0190

# Skeleton-to-coskeleton comparison for a concentrated truncated simplicial object

This leaf owns the degreewise natural comparison, its biproduct matrix, the individual matrix
coefficients, and the resulting monomorphism instances.  The skeleton and coskeleton coordinate
systems remain independently importable from their respective leaves.
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits Opposite Simplicial
open SimplexCategory
open scoped SimplexCategory.Truncated Simplicial

noncomputable section

universe v u

namespace CategoryTheory.SimplicialObject.Truncated

variable {A : Type u} [Category.{v} A]

namespace concentrated.comparison

namespace degree

section Natural

variable [HasZeroObject A] [HasZeroMorphisms A]

/-- In a fixed simplicial degree, the skeleton-to-coskeleton comparison is a natural
transformation in the coefficient object. -/
@[stacks 0190 "natural degreewise concentrated comparison"]
noncomputable def hom (k n : ℕ)
    [SimplicialObject.Truncated.HasPointwiseSkeletons A k]
    [SimplicialObject.Truncated.HasPointwiseCoskeletons A k] :
    skeleton.degree.functor (A := A) k n ⟶
      coskeleton.degree.functor (A := A) k n :=
  Functor.whiskerRight
    (Functor.whiskerLeft (concentrated.functor (A := A) k) (skToCosk (A := A) k))
    ((evaluation SimplexCategoryᵒᵖ A).obj (op ⦋n⦌))

/-- A component of the natural degreewise comparison is the corresponding component of
`skToCosk`. -/
@[simp, stacks 0190 "natural degreewise comparison component"]
theorem hom_app (k n : ℕ)
    [SimplicialObject.Truncated.HasPointwiseSkeletons A k]
    [SimplicialObject.Truncated.HasPointwiseCoskeletons A k] (B : A) :
    (hom (A := A) k n).app B =
      ((skToCosk (A := A) k).app (concentrated B k)).app (op ⦋n⦌) := sorry

end Natural

end degree

namespace matrix

variable [HasZeroObject A] [HasZeroMorphisms A]

/-- The coefficient matrix of the degreewise concentrated comparison, obtained by conjugating
with the natural skeleton and coskeleton biproduct decompositions. -/
@[stacks 0190 "natural concentrated comparison matrix"]
noncomputable def hom (k n : ℕ)
    [∀ X : A, HasBiproduct (fun _ : EpiHom ⦋n⦌ ⦋k⦌ ↦ X)]
    [∀ X : A, HasBiproduct (fun _ : MonoHom ⦋k⦌ ⦋n⦌ ↦ X)]
    [SimplicialObject.Truncated.HasPointwiseSkeletons A k]
    [SimplicialObject.Truncated.HasPointwiseCoskeletons A k] :
    Limits.biproduct.diagonal (C := A) (EpiHom ⦋n⦌ ⦋k⦌) ⟶
      Limits.biproduct.diagonal (C := A) (MonoHom ⦋k⦌ ⦋n⦌) :=
  (skeleton.biproduct.natIso (A := A) k n).inv ≫
    degree.hom (A := A) k n ≫
    (coskeleton.biproduct.natIso (A := A) k n).hom

/-- Objectwise, the natural comparison matrix is the conjugate of the degreewise comparison by
the two biproduct decompositions. -/
@[simp, stacks 0190 "natural comparison matrix component"]
theorem hom_app (k n : ℕ)
    [∀ X : A, HasBiproduct (fun _ : EpiHom ⦋n⦌ ⦋k⦌ ↦ X)]
    [∀ X : A, HasBiproduct (fun _ : MonoHom ⦋k⦌ ⦋n⦌ ↦ X)]
    [SimplicialObject.Truncated.HasPointwiseSkeletons A k]
    [SimplicialObject.Truncated.HasPointwiseCoskeletons A k] (B : A) :
    (hom (A := A) k n).app B =
      (skeleton.biproduct.natIso (A := A) k n).inv.app B ≫
        (degree.hom (A := A) k n).app B ≫
        (coskeleton.biproduct.natIso (A := A) k n).hom.app B := sorry

/-- The natural comparison matrix represents the degreewise comparison under the forward
skeleton and coskeleton biproduct identifications. -/
@[stacks 0190 "comparison matrix conjugation square"]
theorem commutes (k n : ℕ)
    [∀ X : A, HasBiproduct (fun _ : EpiHom ⦋n⦌ ⦋k⦌ ↦ X)]
    [∀ X : A, HasBiproduct (fun _ : MonoHom ⦋k⦌ ⦋n⦌ ↦ X)]
    [SimplicialObject.Truncated.HasPointwiseSkeletons A k]
    [SimplicialObject.Truncated.HasPointwiseCoskeletons A k] :
    (skeleton.biproduct.natIso (A := A) k n).hom ≫ hom (A := A) k n =
      degree.hom (A := A) k n ≫
        (coskeleton.biproduct.natIso (A := A) k n).hom := sorry

/-- The inverse biproduct identifications give the symmetric conjugation formula for the
natural comparison matrix. -/
@[stacks 0190 "inverse comparison matrix conjugation square"]
theorem commutes_inv (k n : ℕ)
    [∀ X : A, HasBiproduct (fun _ : EpiHom ⦋n⦌ ⦋k⦌ ↦ X)]
    [∀ X : A, HasBiproduct (fun _ : MonoHom ⦋k⦌ ⦋n⦌ ↦ X)]
    [SimplicialObject.Truncated.HasPointwiseSkeletons A k]
    [SimplicialObject.Truncated.HasPointwiseCoskeletons A k] :
    hom (A := A) k n ≫ (coskeleton.biproduct.natIso (A := A) k n).inv =
      (skeleton.biproduct.natIso (A := A) k n).inv ≫
        degree.hom (A := A) k n := sorry

/-- A coefficient of the natural comparison matrix is the identity precisely when the monic
index is a section of the epic index, and is zero otherwise. -/
@[stacks 0190 "natural comparison matrix coefficient"]
theorem coeff {k n : ℕ}
    [∀ X : A, HasBiproduct (fun _ : EpiHom ⦋n⦌ ⦋k⦌ ↦ X)]
    [∀ X : A, HasBiproduct (fun _ : MonoHom ⦋k⦌ ⦋n⦌ ↦ X)]
    [SimplicialObject.Truncated.HasPointwiseSkeletons A k]
    [SimplicialObject.Truncated.HasPointwiseCoskeletons A k]
    (a : EpiHom ⦋n⦌ ⦋k⦌) (b : MonoHom ⦋k⦌ ⦋n⦌) :
    Limits.biproduct.diagonal.ι (C := A) a ≫ hom (A := A) k n ≫
        Limits.biproduct.diagonal.π (C := A) b =
      if b.hom ≫ a.hom = 𝟙 ⦋k⦌ then 𝟙 (𝟭 A) else 0 := sorry

/-- Evaluating a coefficient of the natural comparison matrix at `B` recovers the expected
identity-or-zero morphism of `B`. -/
@[stacks 0190 "comparison matrix coefficient component"]
theorem coeff_app {k n : ℕ}
    [∀ X : A, HasBiproduct (fun _ : EpiHom ⦋n⦌ ⦋k⦌ ↦ X)]
    [∀ X : A, HasBiproduct (fun _ : MonoHom ⦋k⦌ ⦋n⦌ ↦ X)]
    [SimplicialObject.Truncated.HasPointwiseSkeletons A k]
    [SimplicialObject.Truncated.HasPointwiseCoskeletons A k]
    (a : EpiHom ⦋n⦌ ⦋k⦌) (b : MonoHom ⦋k⦌ ⦋n⦌) (B : A) :
    Limits.biproduct.ι (fun _ : EpiHom ⦋n⦌ ⦋k⦌ ↦ B) a ≫
        (hom (A := A) k n).app B ≫
        Limits.biproduct.π (fun _ : MonoHom ⦋k⦌ ⦋n⦌ ↦ B) b =
      if b.hom ≫ a.hom = 𝟙 ⦋k⦌ then 𝟙 B else 0 := sorry

end matrix

section Coeff

variable [HasZeroObject A] [HasZeroMorphisms A]

/-- The matrix coefficient of the skeleton-to-coskeleton comparison is the identity precisely
when the monomorphism is a section of the epimorphism, and is zero otherwise. -/
@[stacks 0190 "skeleton-to-coskeleton matrix coefficient"]
theorem coeff (B : A) {k n : ℕ}
    [SimplicialObject.Truncated.HasPointwiseSkeletons A k]
    [SimplicialObject.Truncated.HasPointwiseCoskeletons A k]
    (a : EpiHom ⦋n⦌ ⦋k⦌) (b : MonoHom ⦋k⦌ ⦋n⦌) :
    skeleton.ι B a ≫
        ((skToCosk (A := A) k).app (concentrated B k)).app (op ⦋n⦌) ≫
        coskeleton.π B b =
      if b.hom ≫ a.hom = 𝟙 ⦋k⦌ then 𝟙 B else 0 := sorry

end Coeff

namespace degree

variable [Preadditive A] [HasZeroObject A]

/-- In every degree, the concentrated skeleton-to-coskeleton comparison is a monomorphism under
the chosen pointwise skeleton and coskeleton extensions. -/
@[stacks 0190 "degreewise monomorphism for the concentrated comparison"]
instance mono (B : A) (k n : ℕ)
    [SimplicialObject.Truncated.HasPointwiseSkeletons A k]
    [SimplicialObject.Truncated.HasPointwiseCoskeletons A k] :
    Mono (((skToCosk (A := A) k).app (concentrated B k)).app (op ⦋n⦌)) := sorry

end degree

section Mono

variable [Preadditive A] [HasZeroObject A]

/-- The canonical comparison from the skeleton to the coskeleton of a truncated object
concentrated in one degree is a monomorphism whenever the required pointwise extensions exist. -/
@[stacks 0190 "monomorphism for the concentrated skeleton-to-coskeleton comparison"]
instance mono (B : A) (k : ℕ)
    [SimplicialObject.Truncated.HasPointwiseSkeletons A k]
    [SimplicialObject.Truncated.HasPointwiseCoskeletons A k] :
    Mono ((skToCosk (A := A) k).app (concentrated B k)) := sorry

end Mono

end concentrated.comparison

end CategoryTheory.SimplicialObject.Truncated
