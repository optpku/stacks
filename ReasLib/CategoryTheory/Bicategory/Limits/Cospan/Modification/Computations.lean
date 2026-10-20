/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.CategoryTheory.Bicategory.Limits.Cospan.Modification.Construction
import Mathlib.Tactic.CrossRefAttribute

/-!
# Computations for bicategorical cospan modifications

This leaf contains the reduction API for `CospanTransform.Hom.mk`, together with component
formulas for identity and vertical composition and the reconstruction theorem. Consumers that
only need modification projections and naturality can remain at `Modification.Basic`.
-/

@[expose] public section

open scoped CategoryTheory.Bicategory CategoryTheory.Pseudofunctor.StrongTrans

universe w v u

namespace CategoryTheory.Bicategory.CospanTransform.Hom

variable {B : Type u} [Bicategory.{w, v} B]
variable {x y z x' y' z' : B}
variable {f : x ⟶ z} {g : y ⟶ z} {f' : x' ⟶ z'} {g' : y' ⟶ z'}
variable {ψ φ : CospanTransform f g f' g'}

/-- The left component of `mk` is the supplied cell. -/
@[simp]
theorem mk_left
    (left : ψ.left ⟶ φ.left) (right : ψ.right ⟶ φ.right)
    (base : ψ.base ⟶ φ.base)
    (leftNaturality :
      left ▷ f' ≫ φ.leftIso.hom = ψ.leftIso.hom ≫ f ◁ base)
    (rightNaturality :
      right ▷ g' ≫ φ.rightIso.hom = ψ.rightIso.hom ≫ g ◁ base) :
    Hom.left (mk left right base leftNaturality rightNaturality) = left := sorry

/-- The right component of `mk` is the supplied cell. -/
@[simp]
theorem mk_right
    (left : ψ.left ⟶ φ.left) (right : ψ.right ⟶ φ.right)
    (base : ψ.base ⟶ φ.base)
    (leftNaturality :
      left ▷ f' ≫ φ.leftIso.hom = ψ.leftIso.hom ≫ f ◁ base)
    (rightNaturality :
      right ▷ g' ≫ φ.rightIso.hom = ψ.rightIso.hom ≫ g ◁ base) :
    Hom.right (mk left right base leftNaturality rightNaturality) = right := sorry

/-- The base component of `mk` is the supplied cell. -/
@[simp]
theorem mk_base
    (left : ψ.left ⟶ φ.left) (right : ψ.right ⟶ φ.right)
    (base : ψ.base ⟶ φ.base)
    (leftNaturality :
      left ▷ f' ≫ φ.leftIso.hom = ψ.leftIso.hom ≫ f ◁ base)
    (rightNaturality :
      right ▷ g' ≫ φ.rightIso.hom = ψ.rightIso.hom ≫ g ◁ base) :
    Hom.base (mk left right base leftNaturality rightNaturality) = base := sorry

/-- The left component of an identity modification is an identity cell. -/
@[simp]
theorem id_left (ψ : CospanTransform f g f' g') :
    left (id ψ) = 𝟙 ψ.left := sorry

/-- The right component of an identity modification is an identity cell. -/
@[simp]
theorem id_right (ψ : CospanTransform f g f' g') :
    right (id ψ) = 𝟙 ψ.right := sorry

/-- The base component of an identity modification is an identity cell. -/
@[simp]
theorem id_base (ψ : CospanTransform f g f' g') :
    base (id ψ) = 𝟙 ψ.base := sorry

/-- The left component of a vertical composite is the vertical composite of left components. -/
@[simp]
theorem comp_left
    {χ : CospanTransform f g f' g'}
    (Γ : Pseudofunctor.StrongTrans.Hom ψ φ)
    (Δ : Pseudofunctor.StrongTrans.Hom φ χ) :
    left (comp Γ Δ) = left Γ ≫ left Δ := sorry

/-- The right component of a vertical composite is the vertical composite of right
components. -/
@[simp]
theorem comp_right
    {χ : CospanTransform f g f' g'}
    (Γ : Pseudofunctor.StrongTrans.Hom ψ φ)
    (Δ : Pseudofunctor.StrongTrans.Hom φ χ) :
    right (comp Γ Δ) = right Γ ≫ right Δ := sorry

/-- The base component of a vertical composite is the vertical composite of base components. -/
@[simp]
theorem comp_base
    {χ : CospanTransform f g f' g'}
    (Γ : Pseudofunctor.StrongTrans.Hom ψ φ)
    (Δ : Pseudofunctor.StrongTrans.Hom φ χ) :
    base (comp Γ Δ) = base Γ ≫ base Δ := sorry

/-- Reconstructing a cospan modification from its components and canonical naturality squares
recovers the original modification. -/
@[simp]
theorem mk_components (Γ : Pseudofunctor.StrongTrans.Hom ψ φ) :
    mk (left Γ) (right Γ) (base Γ)
      (left_naturality Γ) (right_naturality Γ) = Γ := sorry

/- Data audit (mathlib 4.32): the readout theorems are proposition-valued interfaces and add no
computational data. The canonical `mk`, `id`, and `comp` owners remain in the preceding leaves. -/

end CategoryTheory.Bicategory.CospanTransform.Hom
