/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.CategoryTheory.Bicategory.Limits.Cospan.Hom.Construction
import Mathlib.Tactic.CrossRefAttribute

/-!
# Computations for bicategorical cospan transformations

This leaf contains the fine-grained reduction API for `CospanTransform.mk`, together with the
identity/composition component formulas and the reconstruction theorem. Consumers which only
need the transformation type and semantic projections can remain at `Cospan.Basic`; consumers
constructing transformations should import `Hom.Construction`.
-/

@[expose] public section

open scoped CategoryTheory.Bicategory CategoryTheory.Pseudofunctor.StrongTrans

universe w v u

namespace CategoryTheory.Bicategory.CospanTransform

variable {B : Type u} [Bicategory.{w, v} B]
variable {x y z x' y' z' x'' y'' z'' : B}
variable {f : x ⟶ z} {g : y ⟶ z} {f' : x' ⟶ z'} {g' : y' ⟶ z'}
variable {f'' : x'' ⟶ z''} {g'' : y'' ⟶ z''}

/-- The left component of `mk` is the supplied left vertex map. -/
@[simp]
theorem mk_left
    (left : x ⟶ x') (right : y ⟶ y') (base : z ⟶ z')
    (leftIso : left ≫ f' ≅ f ≫ base) (rightIso : right ≫ g' ≅ g ≫ base) :
    (mk left right base leftIso rightIso).left = left := by
  rfl

/-- The right component of `mk` is the supplied right vertex map. -/
@[simp]
theorem mk_right
    (left : x ⟶ x') (right : y ⟶ y') (base : z ⟶ z')
    (leftIso : left ≫ f' ≅ f ≫ base) (rightIso : right ≫ g' ≅ g ≫ base) :
    (mk left right base leftIso rightIso).right = right := by
  rfl

/-- The base component of `mk` is the supplied common-target map. -/
@[simp]
theorem mk_base
    (left : x ⟶ x') (right : y ⟶ y') (base : z ⟶ z')
    (leftIso : left ≫ f' ≅ f ≫ base) (rightIso : right ≫ g' ≅ g ≫ base) :
    (mk left right base leftIso rightIso).base = base := by
  rfl

/-- The left generating comparison of `mk` is the supplied comparison. -/
@[simp]
theorem mk_leftIso
    (left : x ⟶ x') (right : y ⟶ y') (base : z ⟶ z')
    (leftIso : left ≫ f' ≅ f ≫ base) (rightIso : right ≫ g' ≅ g ≫ base) :
    (mk left right base leftIso rightIso).leftIso = leftIso := by
  rfl

/-- The right generating comparison of `mk` is the supplied comparison. -/
@[simp]
theorem mk_rightIso
    (left : x ⟶ x') (right : y ⟶ y') (base : z ⟶ z')
    (leftIso : left ≫ f' ≅ f ≫ base) (rightIso : right ≫ g' ≅ g ≫ base) :
    (mk left right base leftIso rightIso).rightIso = rightIso := by
  rfl

/-- The left component of the identity cospan transformation is an identity. -/
@[simp]
theorem id_left (f : x ⟶ z) (g : y ⟶ z) :
    (id f g).left = 𝟙 x := by
  rfl

/-- The right component of the identity cospan transformation is an identity. -/
@[simp]
theorem id_right (f : x ⟶ z) (g : y ⟶ z) :
    (id f g).right = 𝟙 y := by
  rfl

/-- The base component of the identity cospan transformation is an identity. -/
@[simp]
theorem id_base (f : x ⟶ z) (g : y ⟶ z) :
    (id f g).base = 𝟙 z := by
  rfl

/-- The left generating comparison of the identity cospan transformation is the canonical
unitor composite. -/
@[simp]
theorem id_leftIso (f : x ⟶ z) (g : y ⟶ z) :
    (id f g).leftIso = λ_ f ≪≫ (ρ_ f).symm := by
  rfl

/-- The right generating comparison of the identity cospan transformation is the canonical
unitor composite. -/
@[simp]
theorem id_rightIso (f : x ⟶ z) (g : y ⟶ z) :
    (id f g).rightIso = λ_ g ≪≫ (ρ_ g).symm := by
  rfl

/-- The left component of a composite cospan transformation is the composite of the left
components. -/
@[simp]
theorem comp_left
    (ψ : CospanTransform f g f' g') (φ : CospanTransform f' g' f'' g'') :
    (ψ.comp φ).left = ψ.left ≫ φ.left := by
  rfl

/-- The right component of a composite cospan transformation is the composite of the right
components. -/
@[simp]
theorem comp_right
    (ψ : CospanTransform f g f' g') (φ : CospanTransform f' g' f'' g'') :
    (ψ.comp φ).right = ψ.right ≫ φ.right := by
  rfl

/-- The base component of a composite cospan transformation is the composite of the base
components. -/
@[simp]
theorem comp_base
    (ψ : CospanTransform f g f' g') (φ : CospanTransform f' g' f'' g'') :
    (ψ.comp φ).base = ψ.base ≫ φ.base := by
  rfl

/-- The left generating comparison of a composite is the canonical pasting of the two
left generating comparisons. -/
@[simp]
theorem comp_leftIso
    (ψ : CospanTransform f g f' g') (φ : CospanTransform f' g' f'' g'') :
    (ψ.comp φ).leftIso =
      α_ ψ.left φ.left f'' ≪≫
        whiskerLeftIso ψ.left φ.leftIso ≪≫
        (α_ ψ.left f' φ.base).symm ≪≫
        whiskerRightIso ψ.leftIso φ.base ≪≫
        α_ f ψ.base φ.base := by
  apply Iso.ext
  change ((((α_ ψ.left φ.left f'').hom ≫ ψ.left ◁ φ.leftIso.hom) ≫
      (α_ ψ.left f' φ.base).inv) ≫ ψ.leftIso.hom ▷ φ.base) ≫
        (α_ f ψ.base φ.base).hom =
      (α_ ψ.left φ.left f'').hom ≫ ψ.left ◁ φ.leftIso.hom ≫
        (α_ ψ.left f' φ.base).inv ≫ ψ.leftIso.hom ▷ φ.base ≫
          (α_ f ψ.base φ.base).hom
  simp only [Category.assoc]

/-- The right generating comparison of a composite is the canonical pasting of the two
right generating comparisons. -/
@[simp]
theorem comp_rightIso
    (ψ : CospanTransform f g f' g') (φ : CospanTransform f' g' f'' g'') :
    (ψ.comp φ).rightIso =
      α_ ψ.right φ.right g'' ≪≫
        whiskerLeftIso ψ.right φ.rightIso ≪≫
        (α_ ψ.right g' φ.base).symm ≪≫
        whiskerRightIso ψ.rightIso φ.base ≪≫
        α_ g ψ.base φ.base := by
  apply Iso.ext
  change ((((α_ ψ.right φ.right g'').hom ≫ ψ.right ◁ φ.rightIso.hom) ≫
      (α_ ψ.right g' φ.base).inv) ≫ ψ.rightIso.hom ▷ φ.base) ≫
        (α_ g ψ.base φ.base).hom =
      (α_ ψ.right φ.right g'').hom ≫ ψ.right ◁ φ.rightIso.hom ≫
        (α_ ψ.right g' φ.base).inv ≫ ψ.rightIso.hom ▷ φ.base ≫
          (α_ g ψ.base φ.base).hom
  simp only [Category.assoc]

private theorem components_ext
    (ψ φ : CospanTransform f g f' g') (hApp : ψ.app = φ.app)
    (hNat : ∀ (a b : LocallyDiscrete Limits.WalkingCospan) (h : a ⟶ b),
      HEq (ψ.naturality h) (φ.naturality h)) : ψ = φ := by
  rcases ψ with ⟨app₁, naturality₁, h₁, h₂, h₃⟩
  rcases φ with ⟨app₂, naturality₂, k₁, k₂, k₃⟩
  cases hApp
  have h : @naturality₁ = @naturality₂ := by
    funext a b h
    exact eq_of_heq (hNat a b h)
  cases h
  rfl


/-- Reconstructing a cospan transformation from its vertex components and generating
naturality isomorphisms recovers the original strong transformation. -/
@[simp]
theorem mk_components (ψ : CospanTransform f g f' g') :
    mk ψ.left ψ.right ψ.base ψ.leftIso ψ.rightIso = ψ := by
  have hId (a : LocallyDiscrete Limits.WalkingCospan) :
      (ψ.naturality (𝟙 a)).hom =
        (λ_ (ψ.app a)).hom ≫ (ρ_ (ψ.app a)).inv := by
    have h := ψ.naturality_id a
    change (ψ.naturality (𝟙 a)).hom ≫ ψ.app a ◁ 𝟙 _ =
      (𝟙 _) ▷ ψ.app a ≫ (λ_ (ψ.app a)).hom ≫ (ρ_ (ψ.app a)).inv at h
    simpa only [whiskerLeft_id, id_whiskerRight, Category.comp_id, Category.id_comp] using h
  apply components_ext
  · funext a
    rcases a with ⟨a⟩
    cases a with
    | none => rfl
    | some a => cases a <;> rfl
  · rintro ⟨a⟩ ⟨b⟩ ⟨h⟩
    cases h with
    | id a =>
      cases a with
      | none =>
        apply heq_of_eq
        apply Iso.ext
        exact (hId ⟨none⟩).symm
      | some a =>
        cases a <;> apply heq_of_eq <;> apply Iso.ext
        · exact (hId ⟨some Limits.WalkingPair.left⟩).symm
        · exact (hId ⟨some Limits.WalkingPair.right⟩).symm
    | term a => cases a <;> rfl

/- Data and axiom audit (mathlib 4.32): the readout theorems are proposition-valued interfaces;
they add no computational data. The canonical `mk` owner remains in `Hom.Construction`, while
identity and composition data are supplied by `Hom.Basic`. -/

end CategoryTheory.Bicategory.CospanTransform
