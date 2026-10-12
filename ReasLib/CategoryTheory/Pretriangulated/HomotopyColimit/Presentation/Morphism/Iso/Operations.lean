/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import ReasLib.CategoryTheory.Pretriangulated.HomotopyColimit.Presentation.Morphism.Iso.Definition

/-!
# Operations on Invertible Presentation Maps

Reindexing, identity, and composition for maps of telescope presentations whose object maps
are isomorphisms.
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits CategoryTheory.Pretriangulated

universe v u

noncomputable section

namespace CategoryTheory.HomotopyColimit

variable {D : Type u} [Category.{v} D] [Limits.HasZeroObject D] [Preadditive D]
  [HasShift D ℤ] [∀ n : ℤ, (shiftFunctor D n).Additive] [Pretriangulated D]

namespace Presentation.HomWithIso

/-- Reindex an invertible presentation morphism along an equality of diagram morphisms. -/
def rebase {S T : ℕ ⥤ D} {α β : S ⟶ T} {X Y : D}
    {P : Presentation S X} {Q : Presentation T Y}
    (h : α = β) (Φ : HomWithIso α P Q) : HomWithIso β P Q :=
  h ▸ Φ

/-- The identity map of a telescope presentation with its canonical object isomorphism. -/
def id {S : ℕ ⥤ D} {X : D} (P : Presentation S X) : HomWithIso (𝟙 S) P P where
  iso := Iso.refl X
  toCoconeComm := (Presentation.Hom.id P).toCoconeComm
  connectingComm := (Presentation.Hom.id P).connectingComm

/-- Compose invertible maps of explicit telescope presentations. -/
def comp {S₀ S₁ S₂ : ℕ ⥤ D} {α : S₀ ⟶ S₁} {β : S₁ ⟶ S₂}
    {X₀ X₁ X₂ : D} {P : Presentation S₀ X₀} {Q : Presentation S₁ X₁}
    {R : Presentation S₂ X₂} (Φ : HomWithIso α P Q) (Ψ : HomWithIso β Q R) :
    HomWithIso (α ≫ β) P R where
  iso := Φ.iso ≪≫ Ψ.iso
  toCoconeComm := (Φ.toHom.comp Ψ.toHom).toCoconeComm
  connectingComm := (Φ.toHom.comp Ψ.toHom).connectingComm

/-- Rebasing does not change the retained object isomorphism. -/
@[simp]
theorem rebase_iso {S T : ℕ ⥤ D} {α β : S ⟶ T} {X Y : D}
    {P : Presentation S X} {Q : Presentation T Y}
    (h : α = β) (Φ : HomWithIso α P Q) :
    (rebase h Φ).iso = Φ.iso := sorry

/-- Forgetting invertibility commutes with rebasing. -/
@[simp]
theorem rebase_toHom {S T : ℕ ⥤ D} {α β : S ⟶ T} {X Y : D}
    {P : Presentation S X} {Q : Presentation T Y}
    (h : α = β) (Φ : HomWithIso α P Q) :
    (rebase h Φ).toHom = Presentation.Hom.rebase h Φ.toHom := sorry

/-- Rebasing along reflexivity is the identity operation. -/
@[simp]
theorem rebase_rfl {S T : ℕ ⥤ D} {α : S ⟶ T} {X Y : D}
    {P : Presentation S X} {Q : Presentation T Y} (Φ : HomWithIso α P Q) :
    rebase rfl Φ = Φ := sorry

/-- Forgetting invertibility from the identity recovers the identity presentation morphism. -/
@[simp]
theorem id_toHom {S : ℕ ⥤ D} {X : D} (P : Presentation S X) :
    (id P).toHom = Presentation.Hom.id P := sorry

/-- The object isomorphism of the identity presentation map is reflexivity. -/
@[simp]
theorem id_iso {S : ℕ ⥤ D} {X : D} (P : Presentation S X) :
    (id P).iso = Iso.refl X := sorry

/-- Forgetting invertibility commutes with composition of presentation maps. -/
@[simp]
theorem comp_toHom {S₀ S₁ S₂ : ℕ ⥤ D} {α : S₀ ⟶ S₁} {β : S₁ ⟶ S₂}
    {X₀ X₁ X₂ : D} {P : Presentation S₀ X₀} {Q : Presentation S₁ X₁}
    {R : Presentation S₂ X₂} (Φ : HomWithIso α P Q) (Ψ : HomWithIso β Q R) :
    (comp Φ Ψ).toHom = Φ.toHom.comp Ψ.toHom := sorry

/-- The object isomorphism of a composite is the composite object isomorphism. -/
@[simp]
theorem comp_iso {S₀ S₁ S₂ : ℕ ⥤ D} {α : S₀ ⟶ S₁} {β : S₁ ⟶ S₂}
    {X₀ X₁ X₂ : D} {P : Presentation S₀ X₀} {Q : Presentation S₁ X₁}
    {R : Presentation S₂ X₂} (Φ : HomWithIso α P Q) (Ψ : HomWithIso β Q R) :
    (comp Φ Ψ).iso = Φ.iso ≪≫ Ψ.iso := sorry

/-- Left composition by an identity invertible presentation map is the original map after
rebasing along the categorical left-unit law. -/
@[simp]
theorem id_comp {S T : ℕ ⥤ D} {α : S ⟶ T} {X Y : D}
    {P : Presentation S X} {Q : Presentation T Y} (Φ : HomWithIso α P Q) :
    rebase (Category.id_comp α) (comp (id P) Φ) = Φ := sorry

/-- Right composition by an identity invertible presentation map is the original map after
rebasing along the categorical right-unit law. -/
@[simp]
theorem comp_id {S T : ℕ ⥤ D} {α : S ⟶ T} {X Y : D}
    {P : Presentation S X} {Q : Presentation T Y} (Φ : HomWithIso α P Q) :
    rebase (Category.comp_id α) (comp Φ (id Q)) = Φ := sorry

/-- Composition of invertible presentation maps is associative after rebasing along
categorical associativity. -/
@[simp]
theorem comp_assoc
    {S₀ S₁ S₂ S₃ : ℕ ⥤ D} {α : S₀ ⟶ S₁} {β : S₁ ⟶ S₂} {γ : S₂ ⟶ S₃}
    {X₀ X₁ X₂ X₃ : D} {P : Presentation S₀ X₀} {Q : Presentation S₁ X₁}
    {R : Presentation S₂ X₂} {U : Presentation S₃ X₃}
    (Φ : HomWithIso α P Q) (Ψ : HomWithIso β Q R) (Χ : HomWithIso γ R U) :
    rebase (Category.assoc α β γ) (comp (comp Φ Ψ) Χ) = comp Φ (comp Ψ Χ) := sorry

end Presentation.HomWithIso

end CategoryTheory.HomotopyColimit
