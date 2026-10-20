/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.CategoryTheory.Pretriangulated.HomotopyLimit.Presentation.Morphism.Definition

/-!
# Operations on Morphisms of Homotopy-Limit Presentations

Identity, composition, and their algebraic laws for compatible maps of explicit Milnor
presentations.
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits CategoryTheory.Pretriangulated Opposite

noncomputable section

universe u v

namespace CategoryTheory.HomotopyLimit

open SequentialInverseSystem.Milnor

variable {D : Type u} [Category.{v} D] [Limits.HasZeroObject D] [Preadditive D]
  [HasShift D ℤ] [∀ n : ℤ, (shiftFunctor D n).Additive] [Pretriangulated D]

namespace Presentation.Hom

/-- Compatibility with the product inclusions for the identity presentation morphism. -/
theorem id_ιComm {K : SequentialInverseSystem D} {X : D} (P : Presentation K X) :
    CommSq P.ι (𝟙 X) (ProductCone.map P.product P.product (𝟙 K)) P.ι := sorry

/-- Compatibility with the connecting maps for the identity presentation morphism. -/
theorem id_connectingComm {K : SequentialInverseSystem D} {X : D}
    (P : Presentation K X) :
    CommSq P.connecting (ProductCone.map P.product P.product (𝟙 K))
      ((𝟙 X)⟦(1 : ℤ)⟧') P.connecting := sorry

/-- The identity morphism of an explicit homotopy-limit presentation. -/
def id {K : SequentialInverseSystem D} {X : D} (P : Presentation K X) :
    Hom (𝟙 K) P P where
  hom := 𝟙 X
  ιComm := id_ιComm P
  connectingComm := id_connectingComm P

/-- Compatibility with the product inclusions for a composite of presentation morphisms. -/
theorem comp_ιComm
    {K₀ K₁ K₂ : SequentialInverseSystem D} {α : K₀ ⟶ K₁} {β : K₁ ⟶ K₂}
    {X₀ X₁ X₂ : D} {P : Presentation K₀ X₀} {Q : Presentation K₁ X₁}
    {R : Presentation K₂ X₂} (φ : Hom α P Q) (ψ : Hom β Q R) :
    CommSq P.ι (φ.hom ≫ ψ.hom)
      (ProductCone.map P.product R.product (α ≫ β)) R.ι := sorry

/-- Compatibility with the connecting maps for a composite of presentation morphisms. -/
theorem comp_connectingComm
    {K₀ K₁ K₂ : SequentialInverseSystem D} {α : K₀ ⟶ K₁} {β : K₁ ⟶ K₂}
    {X₀ X₁ X₂ : D} {P : Presentation K₀ X₀} {Q : Presentation K₁ X₁}
    {R : Presentation K₂ X₂} (φ : Hom α P Q) (ψ : Hom β Q R) :
    CommSq P.connecting (ProductCone.map P.product R.product (α ≫ β))
      ((φ.hom ≫ ψ.hom)⟦(1 : ℤ)⟧') R.connecting := sorry

/-- Compose compatible morphisms of explicit homotopy-limit presentations. -/
def comp {K₀ K₁ K₂ : SequentialInverseSystem D} {α : K₀ ⟶ K₁} {β : K₁ ⟶ K₂}
    {X₀ X₁ X₂ : D} {P : Presentation K₀ X₀} {Q : Presentation K₁ X₁}
    {R : Presentation K₂ X₂} (φ : Hom α P Q) (ψ : Hom β Q R) :
    Hom (α ≫ β) P R where
  hom := φ.hom ≫ ψ.hom
  ιComm := comp_ιComm φ ψ
  connectingComm := comp_connectingComm φ ψ

/-- Left composition by an identity presentation morphism is the original morphism after
rebasing along the categorical left-unit law. -/
@[simp]
theorem id_comp {K L : SequentialInverseSystem D} {α : K ⟶ L} {X Y : D}
    {P : Presentation K X} {Q : Presentation L Y} (φ : Hom α P Q) :
    rebase (Category.id_comp α) (comp (id P) φ) = φ := sorry

/-- Right composition by an identity presentation morphism is the original morphism after
rebasing along the categorical right-unit law. -/
@[simp]
theorem comp_id {K L : SequentialInverseSystem D} {α : K ⟶ L} {X Y : D}
    {P : Presentation K X} {Q : Presentation L Y} (φ : Hom α P Q) :
    rebase (Category.comp_id α) (comp φ (id Q)) = φ := sorry

/-- Composition of presentation morphisms is associative after rebasing along categorical
associativity. -/
@[simp]
theorem comp_assoc
    {K₀ K₁ K₂ K₃ : SequentialInverseSystem D}
    {α : K₀ ⟶ K₁} {β : K₁ ⟶ K₂} {γ : K₂ ⟶ K₃}
    {X₀ X₁ X₂ X₃ : D} {P : Presentation K₀ X₀} {Q : Presentation K₁ X₁}
    {R : Presentation K₂ X₂} {U : Presentation K₃ X₃}
    (φ : Hom α P Q) (ψ : Hom β Q R) (χ : Hom γ R U) :
    rebase (Category.assoc α β γ) (comp (comp φ ψ) χ) =
      comp φ (comp ψ χ) := sorry

/-- The underlying map of the identity presentation morphism is an identity. -/
@[simp]
theorem id_hom {K : SequentialInverseSystem D} {X : D} (P : Presentation K X) :
    (id P).hom = 𝟙 X := sorry

/-- The underlying map of a composite presentation morphism is the composite of the
underlying maps. -/
@[simp]
theorem comp_hom
    {K₀ K₁ K₂ : SequentialInverseSystem D} {α : K₀ ⟶ K₁} {β : K₁ ⟶ K₂}
    {X₀ X₁ X₂ : D} {P : Presentation K₀ X₀} {Q : Presentation K₁ X₁}
    {R : Presentation K₂ X₂} (φ : Hom α P Q) (ψ : Hom β Q R) :
    (comp φ ψ).hom = φ.hom ≫ ψ.hom := sorry

end Presentation.Hom

end CategoryTheory.HomotopyLimit
