/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
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

/-- Compatibility with the coproduct-to-cocone maps for the identity presentation morphism. -/
theorem id_toCoconeComm {S : ℕ ⥤ D} {X : D} (P : Presentation S X) :
    CommSq P.toCocone
      (ColimitCocone.Discrete.map P.coproduct P.coproduct (𝟙 S : S ⟶ S).app)
      (𝟙 X) P.toCocone := sorry

/-- Compatibility with the connecting maps for the identity presentation morphism. -/
theorem id_connectingComm {S : ℕ ⥤ D} {X : D} (P : Presentation S X) :
    CommSq P.connecting (𝟙 X)
      ((ColimitCocone.Discrete.map P.coproduct P.coproduct (𝟙 S : S ⟶ S).app)⟦(1 : ℤ)⟧')
      P.connecting := sorry

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
      (φ.hom ≫ ψ.hom) R.toCocone := sorry

/-- Compatibility with the connecting maps for a composite of presentation morphisms. -/
theorem comp_connectingComm {S₀ S₁ S₂ : ℕ ⥤ D} {α : S₀ ⟶ S₁} {β : S₁ ⟶ S₂}
    {X₀ X₁ X₂ : D} {P : Presentation S₀ X₀} {Q : Presentation S₁ X₁}
    {R : Presentation S₂ X₂} (φ : Hom α P Q) (ψ : Hom β Q R) :
    CommSq P.connecting (φ.hom ≫ ψ.hom)
      ((ColimitCocone.Discrete.map P.coproduct R.coproduct (α ≫ β).app)⟦(1 : ℤ)⟧')
      R.connecting := sorry

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
    rebase (Category.id_comp α) (comp (id P) φ) = φ := sorry

/-- Right composition by an identity presentation morphism is the original morphism after
rebasing along the categorical right-unit law. -/
@[simp]
theorem comp_id {S T : ℕ ⥤ D} {α : S ⟶ T} {X Y : D}
    {P : Presentation S X} {Q : Presentation T Y} (φ : Hom α P Q) :
    rebase (Category.comp_id α) (comp φ (id Q)) = φ := sorry

/-- Composition of presentation morphisms is associative after rebasing along categorical
associativity. -/
@[simp]
theorem comp_assoc
    {S₀ S₁ S₂ S₃ : ℕ ⥤ D} {α : S₀ ⟶ S₁} {β : S₁ ⟶ S₂} {γ : S₂ ⟶ S₃}
    {X₀ X₁ X₂ X₃ : D} {P : Presentation S₀ X₀} {Q : Presentation S₁ X₁}
    {R : Presentation S₂ X₂} {U : Presentation S₃ X₃}
    (φ : Hom α P Q) (ψ : Hom β Q R) (χ : Hom γ R U) :
    rebase (Category.assoc α β γ) (comp (comp φ ψ) χ) = comp φ (comp ψ χ) := sorry

/-- The underlying map of the identity presentation morphism is an identity. -/
@[simp]
theorem id_hom {S : ℕ ⥤ D} {X : D} (P : Presentation S X) :
    (id P).hom = 𝟙 X := sorry

/-- The underlying map of a composite presentation morphism is the composite of the
underlying maps. -/
@[simp]
theorem comp_hom {S₀ S₁ S₂ : ℕ ⥤ D} {α : S₀ ⟶ S₁} {β : S₁ ⟶ S₂}
    {X₀ X₁ X₂ : D} {P : Presentation S₀ X₀} {Q : Presentation S₁ X₁}
    {R : Presentation S₂ X₂} (φ : Hom α P Q) (ψ : Hom β Q R) :
    (comp φ ψ).hom = φ.hom ≫ ψ.hom := sorry

end Presentation.Hom

end CategoryTheory.HomotopyColimit
