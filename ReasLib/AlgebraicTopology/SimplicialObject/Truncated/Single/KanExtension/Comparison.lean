/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
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
      ((skToCosk (A := A) k).app (concentrated B k)).app (op ⦋n⦌) := rfl

end Natural

end degree

section Coeff

variable [HasZeroObject A] [HasZeroMorphisms A]

set_option backward.isDefEq.respectTransparency false in
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
      if b.hom ≫ a.hom = 𝟙 ⦋k⦌ then 𝟙 B else 0 := by
  classical
  let L := (SimplexCategory.Truncated.inclusion k).op
  let U := concentrated B k
  let c : U.skeleton ⟶ U.coskeleton := (skToCosk (A := A) k).app U
  let ε := L.rightKanExtensionCounit U
  let e := Functor.LeftKanExtension.unitIso L U
  have hc := skToCosk.homEquiv.symm_app (A := A) k U
  rw [Adjunction.homEquiv_counit] at hc
  simp only [SimplicialObject.coskAdj, Functor.ranAdjunction_counit] at hc
  change L.whiskerLeft c ≫ ε = e.inv at hc
  have hc_top := congrArg (fun f ↦ f.app (op (top k))) hc
  change c.app (op ⦋k⦌) ≫ ε.app (op (top k)) = (e.app (op (top k))).inv at hc_top
  have hnat :
      skeleton.ι B a ≫ c.app (op ⦋n⦌) ≫ coskeleton.π B b =
        (skeleton.ι B a ≫ U.skeleton.map b.hom.op) ≫
          c.app (op ⦋k⦌) ≫ ε.app (op (top k)) ≫ topInv B k := by
    rw [coskeleton.π.eq_map_counit]
    simp only [Category.assoc]
    rw [← c.naturality_assoc]
  rw [hnat]
  by_cases hab : b.hom ≫ a.hom = 𝟙 ⦋k⦌
  · letI : Epi (b.hom ≫ a.hom) := by rw [hab]; infer_instance
    rw [if_pos hab, skeleton.map_ι_of_epi, skeleton.ι.eq_unit_map]
    simp only [hab, EpiHom.hom, Category.assoc]
    change topHom B k ≫ e.hom.app (op (top k)) ≫
      U.skeleton.map (𝟙 (L.obj (op (top k)))) ≫
      c.app (op ⦋k⦌) ≫ ε.app (op (top k)) ≫ topInv B k = 𝟙 B
    rw [Functor.map_id]
    erw [Category.id_comp]
    rw [← Category.assoc (c.app (op ⦋k⦌)) (ε.app (op (top k))) (topInv B k),
      hc_top]
    change topHom B k ≫ e.hom.app (op (top k)) ≫
      e.inv.app (op (top k)) ≫ topInv B k = 𝟙 B
    rw [e.hom_inv_id_app_assoc, topHom_comp_topInv]
  · have hnot : ¬ Epi (b.hom ≫ a.hom) := by
      intro h
      exact hab (SimplexCategory.eq_id_of_epi (b.hom ≫ a.hom))
    rw [if_neg hab, skeleton.map_ι_of_not_epi B b.hom a hnot]
    simp only [zero_comp]

end Coeff

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
        (coskeleton.biproduct.natIso (A := A) k n).hom.app B := rfl

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
        (coskeleton.biproduct.natIso (A := A) k n).hom := by
  simp only [hom, Iso.hom_inv_id_assoc]

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
        degree.hom (A := A) k n := by
  simp only [hom, Category.assoc, Iso.hom_inv_id, Category.comp_id]

set_option backward.isDefEq.respectTransparency false in
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
      if b.hom ≫ a.hom = 𝟙 ⦋k⦌ then 𝟙 (𝟭 A) else 0 := by
  classical
  calc
    _ = (Limits.biproduct.diagonal.ι (C := A) a ≫
          (skeleton.biproduct.natIso (A := A) k n).inv) ≫
        degree.hom (A := A) k n ≫
        ((coskeleton.biproduct.natIso (A := A) k n).hom ≫
          Limits.biproduct.diagonal.π (C := A) b) := by
      simp only [hom, Category.assoc]
    _ = skeleton.degree.ι (A := A) a ≫ degree.hom (A := A) k n ≫
        coskeleton.degree.π (A := A) b := by
      rw [skeleton.biproduct.natIso.ι_inv, coskeleton.biproduct.natIso.hom_π]
    _ = _ := by
      ext B
      have h := concentrated.comparison.coeff B a b
      by_cases hab : b.hom ≫ a.hom = 𝟙 ⦋k⦌
      · simpa only [NatTrans.comp_app, skeleton.degree.ι_app, degree.hom_app,
          coskeleton.degree.π_app, if_pos hab, NatTrans.id_app, Functor.id_obj] using h
      · simpa only [NatTrans.comp_app, skeleton.degree.ι_app, degree.hom_app,
          coskeleton.degree.π_app, if_neg hab, zero_app, Functor.id_obj] using h

set_option backward.isDefEq.respectTransparency false in
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
      if b.hom ≫ a.hom = 𝟙 ⦋k⦌ then 𝟙 B else 0 := by
  classical
  have h := congrArg (fun f ↦ f.app B) (coeff (A := A) a b)
  by_cases hab : b.hom ≫ a.hom = 𝟙 ⦋k⦌
  · simpa only [if_pos hab, NatTrans.comp_app, Limits.biproduct.diagonal.ι_app,
      Limits.biproduct.diagonal.π_app, NatTrans.id_app, Functor.id_obj] using h
  · simpa only [if_neg hab, NatTrans.comp_app, Limits.biproduct.diagonal.ι_app,
      Limits.biproduct.diagonal.π_app, zero_app, Functor.id_obj] using h

end matrix

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
    Mono ((skToCosk (A := A) k).app (concentrated B k)) := by
  haveI : ∀ X : SimplexCategoryᵒᵖ,
      Mono (((skToCosk (A := A) k).app (concentrated B k)).app X) := by
    intro X
    obtain ⟨⟨n⟩⟩ := X
    exact degree.mono B k n
  exact NatTrans.mono_of_mono_app _

end Mono

end concentrated.comparison

end CategoryTheory.SimplicialObject.Truncated
