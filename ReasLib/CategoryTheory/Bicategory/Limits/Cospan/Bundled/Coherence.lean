/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.CategoryTheory.Bicategory.Limits.Cospan.Bundled.Modification

/-!
# Coherence computations for bundled bicategorical cospans

This file exposes the componentwise behavior of the bicategory structure inherited by bundled
cospans: left and right whiskering, associators, and unitors. Each statement reduces a bundled
coherence cell to the corresponding ambient coherence cell at the left, right, or common-target
vertex.
-/

@[expose] public section

open scoped CategoryTheory.Bicategory CategoryTheory.Pseudofunctor.StrongTrans

universe w v u

namespace CategoryTheory.Bicategory.Cospan.Hom₂

variable {B : Type u} [Bicategory.{w, v} B]
variable {S T : Cospan B}

/-- Left whiskering computes by left whiskering at the left endpoint. -/
@[simp]
theorem whiskerLeft_left
    {R S T : Cospan B} (ψ : R ⟶ S)
    {φ χ : S ⟶ T} (Γ : φ ⟶ χ) :
    left (ψ ◁ Γ) = Hom.left ψ ◁ left Γ := sorry

/-- Left whiskering computes by left whiskering at the right endpoint. -/
@[simp]
theorem whiskerLeft_right
    {R S T : Cospan B} (ψ : R ⟶ S)
    {φ χ : S ⟶ T} (Γ : φ ⟶ χ) :
    right (ψ ◁ Γ) = Hom.right ψ ◁ right Γ := sorry

/-- Left whiskering computes by left whiskering at the common target. -/
@[simp]
theorem whiskerLeft_base
    {R S T : Cospan B} (ψ : R ⟶ S)
    {φ χ : S ⟶ T} (Γ : φ ⟶ χ) :
    base (ψ ◁ Γ) = Hom.base ψ ◁ base Γ := sorry

/-- Right whiskering computes by right whiskering at the left endpoint. -/
@[simp]
theorem whiskerRight_left
    {R S T : Cospan B} {ψ φ : R ⟶ S}
    (Γ : ψ ⟶ φ) (χ : S ⟶ T) :
    left (Γ ▷ χ) = left Γ ▷ Hom.left χ := sorry

/-- Right whiskering computes by right whiskering at the right endpoint. -/
@[simp]
theorem whiskerRight_right
    {R S T : Cospan B} {ψ φ : R ⟶ S}
    (Γ : ψ ⟶ φ) (χ : S ⟶ T) :
    right (Γ ▷ χ) = right Γ ▷ Hom.right χ := sorry

/-- Right whiskering computes by right whiskering at the common target. -/
@[simp]
theorem whiskerRight_base
    {R S T : Cospan B} {ψ φ : R ⟶ S}
    (Γ : ψ ⟶ φ) (χ : S ⟶ T) :
    base (Γ ▷ χ) = base Γ ▷ Hom.base χ := sorry

/-- The left component of the forward cospan associator is the ambient associator. -/
@[simp]
theorem associator_hom_left
    {R S T U : Cospan B}
    (ψ : R ⟶ S) (φ : S ⟶ T) (χ : T ⟶ U) :
    left ((α_ ψ φ χ).hom) =
      (α_ (Hom.left ψ) (Hom.left φ) (Hom.left χ)).hom := sorry

/-- The right component of the forward cospan associator is the ambient associator. -/
@[simp]
theorem associator_hom_right
    {R S T U : Cospan B}
    (ψ : R ⟶ S) (φ : S ⟶ T) (χ : T ⟶ U) :
    right ((α_ ψ φ χ).hom) =
      (α_ (Hom.right ψ) (Hom.right φ) (Hom.right χ)).hom := sorry

/-- The common-target component of the forward cospan associator is the ambient
associator. -/
@[simp]
theorem associator_hom_base
    {R S T U : Cospan B}
    (ψ : R ⟶ S) (φ : S ⟶ T) (χ : T ⟶ U) :
    base ((α_ ψ φ χ).hom) =
      (α_ (Hom.base ψ) (Hom.base φ) (Hom.base χ)).hom := sorry

/-- The left component of the inverse cospan associator is the inverse ambient associator. -/
@[simp]
theorem associator_inv_left
    {R S T U : Cospan B}
    (ψ : R ⟶ S) (φ : S ⟶ T) (χ : T ⟶ U) :
    left ((α_ ψ φ χ).inv) =
      (α_ (Hom.left ψ) (Hom.left φ) (Hom.left χ)).inv := sorry

/-- The right component of the inverse cospan associator is the inverse ambient
associator. -/
@[simp]
theorem associator_inv_right
    {R S T U : Cospan B}
    (ψ : R ⟶ S) (φ : S ⟶ T) (χ : T ⟶ U) :
    right ((α_ ψ φ χ).inv) =
      (α_ (Hom.right ψ) (Hom.right φ) (Hom.right χ)).inv := sorry

/-- The common-target component of the inverse cospan associator is the inverse ambient
associator. -/
@[simp]
theorem associator_inv_base
    {R S T U : Cospan B}
    (ψ : R ⟶ S) (φ : S ⟶ T) (χ : T ⟶ U) :
    base ((α_ ψ φ χ).inv) =
      (α_ (Hom.base ψ) (Hom.base φ) (Hom.base χ)).inv := sorry

/-- The left component of the forward cospan left unitor is the ambient left unitor. -/
@[simp]
theorem leftUnitor_hom_left (ψ : S ⟶ T) :
    left ((λ_ ψ).hom) = (λ_ (Hom.left ψ)).hom := sorry

/-- The right component of the forward cospan left unitor is the ambient left unitor. -/
@[simp]
theorem leftUnitor_hom_right (ψ : S ⟶ T) :
    right ((λ_ ψ).hom) = (λ_ (Hom.right ψ)).hom := sorry

/-- The common-target component of the forward cospan left unitor is the ambient left
unitor. -/
@[simp]
theorem leftUnitor_hom_base (ψ : S ⟶ T) :
    base ((λ_ ψ).hom) = (λ_ (Hom.base ψ)).hom := sorry

/-- The left component of the inverse cospan left unitor is the inverse ambient left
unitor. -/
@[simp]
theorem leftUnitor_inv_left (ψ : S ⟶ T) :
    left ((λ_ ψ).inv) = (λ_ (Hom.left ψ)).inv := sorry

/-- The right component of the inverse cospan left unitor is the inverse ambient left
unitor. -/
@[simp]
theorem leftUnitor_inv_right (ψ : S ⟶ T) :
    right ((λ_ ψ).inv) = (λ_ (Hom.right ψ)).inv := sorry

/-- The common-target component of the inverse cospan left unitor is the inverse ambient
left unitor. -/
@[simp]
theorem leftUnitor_inv_base (ψ : S ⟶ T) :
    base ((λ_ ψ).inv) = (λ_ (Hom.base ψ)).inv := sorry

/-- The left component of the forward cospan right unitor is the ambient right unitor. -/
@[simp]
theorem rightUnitor_hom_left (ψ : S ⟶ T) :
    left ((ρ_ ψ).hom) = (ρ_ (Hom.left ψ)).hom := sorry

/-- The right component of the forward cospan right unitor is the ambient right unitor. -/
@[simp]
theorem rightUnitor_hom_right (ψ : S ⟶ T) :
    right ((ρ_ ψ).hom) = (ρ_ (Hom.right ψ)).hom := sorry

/-- The common-target component of the forward cospan right unitor is the ambient right
unitor. -/
@[simp]
theorem rightUnitor_hom_base (ψ : S ⟶ T) :
    base ((ρ_ ψ).hom) = (ρ_ (Hom.base ψ)).hom := sorry

/-- The left component of the inverse cospan right unitor is the inverse ambient right
unitor. -/
@[simp]
theorem rightUnitor_inv_left (ψ : S ⟶ T) :
    left ((ρ_ ψ).inv) = (ρ_ (Hom.left ψ)).inv := sorry

/-- The right component of the inverse cospan right unitor is the inverse ambient right
unitor. -/
@[simp]
theorem rightUnitor_inv_right (ψ : S ⟶ T) :
    right ((ρ_ ψ).inv) = (ρ_ (Hom.right ψ)).inv := sorry

/-- The common-target component of the inverse cospan right unitor is the inverse ambient
right unitor. -/
@[simp]
theorem rightUnitor_inv_base (ψ : S ⟶ T) :
    base ((ρ_ ψ).inv) = (ρ_ (Hom.base ψ)).inv := sorry

/- This module introduces no data-bearing declaration. Every statement is the projection of
the induced bicategory's canonical coherence cell to one of the three cospan vertices. -/

end CategoryTheory.Bicategory.Cospan.Hom₂

namespace CategoryTheory.Bicategory.Cospan

variable {B : Type u} [Bicategory.{w, v} B]

/-- The unit comparison of the strict inclusion of bundled cospans into walking-cospan
pseudofunctors is reflexivity. -/
@[simp]
theorem inclusion_mapId (S : Cospan B) :
    (inclusion B).mapId S = Iso.refl (𝟙 S.diagram) := sorry

/-- The composition comparison of the strict inclusion of bundled cospans into walking-cospan
pseudofunctors is the canonical equality isomorphism supplied by strictness. -/
@[simp]
theorem inclusion_mapComp
    {R S T : Cospan B} (ψ : R ⟶ S) (φ : S ⟶ T) :
    (inclusion B).mapComp ψ φ =
      eqToIso ((inclusion B).map_comp ψ φ) := sorry

end CategoryTheory.Bicategory.Cospan
