/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.CategoryTheory.Pretriangulated.HomotopyColimit.Presentation.Morphism.Definition

/-!
# Operations on Morphisms of Telescope Presentations

Identity, composition, and their algebraic laws for compatible maps of explicit telescope
presentations.
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits CategoryTheory.Pretriangulated

universe v u

noncomputable section

namespace CategoryTheory.HomotopyColimit

open Limits.Sequential

variable {D : Type u} [Category.{v} D] [Limits.HasZeroObject D] [Preadditive D]
  [HasShift D ℤ] [∀ n : ℤ, (shiftFunctor D n).Additive] [Pretriangulated D]

namespace Presentation.Hom

section

omit [HasZeroObject D] [Preadditive D] [HasShift D ℤ]
  [∀ n : ℤ, (shiftFunctor D n).Additive] [Pretriangulated D]

private theorem coproductMap_id {S : ℕ ⥤ D}
    (P : ColimitCocone (Discrete.functor S.obj)) :
    ColimitCocone.Discrete.map P P (𝟙 S : S ⟶ S).app = 𝟙 P.cocone.pt := by
  apply P.isColimit.hom_ext
  intro n
  simp only [ColimitCocone.Discrete.map, ColimitCocone.map, IsColimit.ι_map,
    Discrete.natTrans_app, NatTrans.id_app, Category.comp_id]
  exact Category.id_comp _

private theorem coproductMap_comp {S₀ S₁ S₂ : ℕ ⥤ D}
    (P : ColimitCocone (Discrete.functor S₀.obj))
    (Q : ColimitCocone (Discrete.functor S₁.obj))
    (R : ColimitCocone (Discrete.functor S₂.obj)) (α : S₀ ⟶ S₁) (β : S₁ ⟶ S₂) :
    ColimitCocone.Discrete.map P Q α.app ≫ ColimitCocone.Discrete.map Q R β.app =
      ColimitCocone.Discrete.map P R (α ≫ β).app := by
  apply P.isColimit.hom_ext
  intro n
  simp only [ColimitCocone.Discrete.map, ColimitCocone.map,
    IsColimit.ι_map, IsColimit.ι_map_assoc, Discrete.natTrans_app, NatTrans.comp_app]
  exact (Category.assoc _ _ _).symm

end

private theorem rebase_eq_of_hom_eq {S T : ℕ ⥤ D} {α β : S ⟶ T} {X Y : D}
    {P : Presentation S X} {Q : Presentation T Y}
    (h : α = β) (φ : Hom α P Q) (ψ : Hom β P Q) (hhom : φ.hom = ψ.hom) :
    rebase h φ = ψ := by
  cases h
  cases φ
  cases ψ
  cases hhom
  rfl

/-- Compatibility with the coproduct-to-cocone maps for the identity presentation morphism. -/
theorem id_toCoconeComm {S : ℕ ⥤ D} {X : D} (P : Presentation S X) :
    CommSq P.toCocone
      (ColimitCocone.Discrete.map P.coproduct P.coproduct (𝟙 S : S ⟶ S).app)
      (𝟙 X) P.toCocone := by
  constructor
  rw [coproductMap_id, Category.comp_id, Category.id_comp]

/-- Compatibility with the connecting maps for the identity presentation morphism. -/
theorem id_connectingComm {S : ℕ ⥤ D} {X : D} (P : Presentation S X) :
    CommSq P.connecting (𝟙 X)
      ((ColimitCocone.Discrete.map P.coproduct P.coproduct (𝟙 S : S ⟶ S).app)⟦(1 : ℤ)⟧')
      P.connecting := by
  constructor
  rw [coproductMap_id, Functor.map_id, Category.comp_id, Category.id_comp]

/-- The identity morphism of an explicit telescope presentation. -/
def id {S : ℕ ⥤ D} {X : D} (P : Presentation S X) : Hom (𝟙 S) P P where
  hom := 𝟙 X
  toCoconeComm := id_toCoconeComm P
  connectingComm := id_connectingComm P

/-- Compatibility with the coproduct-to-cocone maps for a composite of presentation
morphisms. -/
theorem comp_toCoconeComm {S₀ S₁ S₂ : ℕ ⥤ D} {α : S₀ ⟶ S₁} {β : S₁ ⟶ S₂}
    {X₀ X₁ X₂ : D} {P : Presentation S₀ X₀} {Q : Presentation S₁ X₁}
    {R : Presentation S₂ X₂} (φ : Hom α P Q) (ψ : Hom β Q R) :
    CommSq P.toCocone (ColimitCocone.Discrete.map P.coproduct R.coproduct (α ≫ β).app)
      (φ.hom ≫ ψ.hom) R.toCocone := by
  rw [← coproductMap_comp P.coproduct Q.coproduct R.coproduct α β]
  exact φ.toCoconeComm.vert_comp ψ.toCoconeComm

/-- Compatibility with the connecting maps for a composite of presentation morphisms. -/
theorem comp_connectingComm {S₀ S₁ S₂ : ℕ ⥤ D} {α : S₀ ⟶ S₁} {β : S₁ ⟶ S₂}
    {X₀ X₁ X₂ : D} {P : Presentation S₀ X₀} {Q : Presentation S₁ X₁}
    {R : Presentation S₂ X₂} (φ : Hom α P Q) (ψ : Hom β Q R) :
    CommSq P.connecting (φ.hom ≫ ψ.hom)
      ((ColimitCocone.Discrete.map P.coproduct R.coproduct (α ≫ β).app)⟦(1 : ℤ)⟧')
      R.connecting := by
  rw [← coproductMap_comp P.coproduct Q.coproduct R.coproduct α β, Functor.map_comp]
  exact φ.connectingComm.vert_comp ψ.connectingComm

/-- Compose compatible morphisms of explicit telescope presentations. -/
def comp {S₀ S₁ S₂ : ℕ ⥤ D} {α : S₀ ⟶ S₁} {β : S₁ ⟶ S₂}
    {X₀ X₁ X₂ : D} {P : Presentation S₀ X₀} {Q : Presentation S₁ X₁}
    {R : Presentation S₂ X₂} (φ : Hom α P Q) (ψ : Hom β Q R) :
    Hom (α ≫ β) P R where
  hom := φ.hom ≫ ψ.hom
  toCoconeComm := comp_toCoconeComm φ ψ
  connectingComm := comp_connectingComm φ ψ

/-- Left composition by an identity presentation morphism is the original morphism after
rebasing along the categorical left-unit law. -/
@[simp]
theorem id_comp {S T : ℕ ⥤ D} {α : S ⟶ T} {X Y : D}
    {P : Presentation S X} {Q : Presentation T Y} (φ : Hom α P Q) :
    rebase (Category.id_comp α) (comp (id P) φ) = φ := by
  apply rebase_eq_of_hom_eq
  exact Category.id_comp φ.hom

/-- Right composition by an identity presentation morphism is the original morphism after
rebasing along the categorical right-unit law. -/
@[simp]
theorem comp_id {S T : ℕ ⥤ D} {α : S ⟶ T} {X Y : D}
    {P : Presentation S X} {Q : Presentation T Y} (φ : Hom α P Q) :
    rebase (Category.comp_id α) (comp φ (id Q)) = φ := by
  apply rebase_eq_of_hom_eq
  exact Category.comp_id φ.hom

/-- Composition of presentation morphisms is associative after rebasing along categorical
associativity. -/
@[simp]
theorem comp_assoc
    {S₀ S₁ S₂ S₃ : ℕ ⥤ D} {α : S₀ ⟶ S₁} {β : S₁ ⟶ S₂} {γ : S₂ ⟶ S₃}
    {X₀ X₁ X₂ X₃ : D} {P : Presentation S₀ X₀} {Q : Presentation S₁ X₁}
    {R : Presentation S₂ X₂} {U : Presentation S₃ X₃}
    (φ : Hom α P Q) (ψ : Hom β Q R) (χ : Hom γ R U) :
    rebase (Category.assoc α β γ) (comp (comp φ ψ) χ) = comp φ (comp ψ χ) := by
  apply rebase_eq_of_hom_eq
  exact Category.assoc φ.hom ψ.hom χ.hom

/-- The underlying map of the identity presentation morphism is an identity. -/
@[simp]
theorem id_hom {S : ℕ ⥤ D} {X : D} (P : Presentation S X) :
    (id P).hom = 𝟙 X := rfl

/-- The underlying map of a composite presentation morphism is the composite of the
underlying maps. -/
@[simp]
theorem comp_hom {S₀ S₁ S₂ : ℕ ⥤ D} {α : S₀ ⟶ S₁} {β : S₁ ⟶ S₂}
    {X₀ X₁ X₂ : D} {P : Presentation S₀ X₀} {Q : Presentation S₁ X₁}
    {R : Presentation S₂ X₂} (φ : Hom α P Q) (ψ : Hom β Q R) :
    (comp φ ψ).hom = φ.hom ≫ ψ.hom := rfl

end Presentation.Hom

end CategoryTheory.HomotopyColimit
