/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import Mathlib.CategoryTheory.Bicategory.LocallyGroupoid
public import ReasLib.CategoryTheory.Bicategory.Comma.Basic.Bicategory

@[expose] public section

/-!
# Colax comma computations

This leaf exposes the componentwise computation theorems and local-groupoid
inheritance for the assembled colax comma bicategory. These are the intended
rewriting API for projections, pseudofunctorial maps, and later constructions.
-/

universe wA vA uA wB vB uB wC vC uC

namespace CategoryTheory

open Bicategory
open scoped Bicategory

namespace Bicategory

variable {A : Type uA} [Bicategory.{wA, vA} A]
variable {B : Type uB} [Bicategory.{wB, vB} B]
variable {C : Type uC} [Bicategory.{wC, vC} C]

namespace ColaxComma

variable {F : A ⥤ᵖ C} {G : B ⥤ᵖ C}

/-- The left endpoint of the canonical identity `1`-morphism is the ambient identity. -/
@[simp]
theorem id_left (S : ColaxComma F G) :
    (𝟙 S : S ⟶ S).left = 𝟙 S.left := sorry
/- Proof strategy: unfold the public bicategory instance and project the private identity data. -/

/-- The right endpoint of the canonical identity `1`-morphism is the ambient identity. -/
@[simp]
theorem id_right (S : ColaxComma F G) :
    (𝟙 S : S ⟶ S).right = 𝟙 S.right := sorry
/- Proof strategy: unfold the public bicategory instance and project the private identity data. -/

/-- Horizontal composition is computed componentwise on left endpoints. -/
@[simp]
theorem comp_left {S T U : ColaxComma F G} (f : S ⟶ T) (g : T ⟶ U) :
    (f ≫ g).left = f.left ≫ g.left := sorry
/- Proof strategy: unfold the public bicategory instance and project the private composite data. -/

/-- Horizontal composition is computed componentwise on right endpoints. -/
@[simp]
theorem comp_right {S T U : ColaxComma F G} (f : S ⟶ T) (g : T ⟶ U) :
    (f ≫ g).right = f.right ≫ g.right := sorry
/- Proof strategy: unfold the public bicategory instance and project the private composite data. -/

/-- The comparison cell of the canonical identity `1`-morphism is the standard unitor pasting. -/
@[simp]
theorem id_cell (S : ColaxComma F G) :
    (𝟙 S : S ⟶ S).cell =
      ((F.mapId S.left).hom ▷ S.hom) ≫
        (λ_ S.hom).hom ≫ (ρ_ S.hom).inv ≫
          (S.hom ◁ (G.mapId S.right).inv) := sorry
/- Proof strategy: unfold the public bicategory instance and the private identity comparison cell. -/

/-- The comparison cell of a canonical composite is the standard seven-stage comma pasting.
This theorem is intentionally not a simp lemma: automatic expansion would obscure downstream
statements, while the named equation remains available to proofs that need the complete cell. -/
theorem comp_cell {S T U : ColaxComma F G} (f : S ⟶ T) (g : T ⟶ U) :
    (f ≫ g).cell =
      ((F.mapComp f.left g.left).hom ▷ U.hom) ≫
        (α_ (F.map f.left) (F.map g.left) U.hom).hom ≫
          (F.map f.left ◁ g.cell) ≫
            (α_ (F.map f.left) T.hom (G.map g.right)).inv ≫
              (f.cell ▷ G.map g.right) ≫
                (α_ S.hom (G.map f.right) (G.map g.right)).hom ≫
                  (S.hom ◁ (G.mapComp f.right g.right).inv) := sorry
/- Proof strategy: unfold the public bicategory instance and the private composite comparison cell. -/

/-- Identity `2`-morphisms are computed componentwise on left endpoints. -/
@[simp]
theorem id₂_left {S T : ColaxComma F G} (f : S ⟶ T) :
    (𝟙 f : f ⟶ f).left = 𝟙 f.left := sorry
/- Proof strategy: unfold the hom-category supplied by the public bicategory instance. -/

/-- Identity `2`-morphisms are computed componentwise on right endpoints. -/
@[simp]
theorem id₂_right {S T : ColaxComma F G} (f : S ⟶ T) :
    (𝟙 f : f ⟶ f).right = 𝟙 f.right := sorry
/- Proof strategy: unfold the hom-category supplied by the public bicategory instance. -/

/-- Vertical composition is computed componentwise on left endpoint cells. -/
@[simp]
theorem comp₂_left {S T : ColaxComma F G} {f g h : S ⟶ T}
    (η : f ⟶ g) (θ : g ⟶ h) :
    (η ≫ θ).left = η.left ≫ θ.left := sorry
/- Proof strategy: unfold the hom-category supplied by the public bicategory instance. -/

/-- Vertical composition is computed componentwise on right endpoint cells. -/
@[simp]
theorem comp₂_right {S T : ColaxComma F G} {f g h : S ⟶ T}
    (η : f ⟶ g) (θ : g ⟶ h) :
    (η ≫ θ).right = η.right ≫ θ.right := sorry
/- Proof strategy: unfold the hom-category supplied by the public bicategory instance. -/

/-- Left whiskering is computed by ambient left whiskering on left endpoint cells. -/
@[simp]
theorem whiskerLeft_left {S T U : ColaxComma F G} (f : S ⟶ T)
    {g h : T ⟶ U} (η : g ⟶ h) :
    (f ◁ η).left = f.left ◁ η.left := sorry
/- Proof strategy: unfold the public bicategory instance and project its left-whiskering data. -/

/-- Left whiskering is computed by ambient left whiskering on right endpoint cells. -/
@[simp]
theorem whiskerLeft_right {S T U : ColaxComma F G} (f : S ⟶ T)
    {g h : T ⟶ U} (η : g ⟶ h) :
    (f ◁ η).right = f.right ◁ η.right := sorry
/- Proof strategy: unfold the public bicategory instance and project its left-whiskering data. -/

/-- Right whiskering is computed by ambient right whiskering on left endpoint cells. -/
@[simp]
theorem whiskerRight_left {S T U : ColaxComma F G} {f g : S ⟶ T}
    (η : f ⟶ g) (h : T ⟶ U) :
    (η ▷ h).left = η.left ▷ h.left := sorry
/- Proof strategy: unfold the public bicategory instance and project its right-whiskering data. -/

/-- Right whiskering is computed by ambient right whiskering on right endpoint cells. -/
@[simp]
theorem whiskerRight_right {S T U : ColaxComma F G} {f g : S ⟶ T}
    (η : f ⟶ g) (h : T ⟶ U) :
    (η ▷ h).right = η.right ▷ h.right := sorry
/- Proof strategy: unfold the public bicategory instance and project its right-whiskering data. -/

/-- The forward left-unitor cell projects to the ambient left unitor on left endpoints. -/
@[simp]
theorem leftUnitor_hom_left {S T : ColaxComma F G} (f : S ⟶ T) :
    (λ_ f).hom.left = (λ_ f.left).hom := sorry
/- Proof strategy: unfold the public bicategory instance and project the private comma unitor. -/

/-- The forward left-unitor cell projects to the ambient left unitor on right endpoints. -/
@[simp]
theorem leftUnitor_hom_right {S T : ColaxComma F G} (f : S ⟶ T) :
    (λ_ f).hom.right = (λ_ f.right).hom := sorry
/- Proof strategy: unfold the public bicategory instance and project the private comma unitor. -/

/-- The forward right-unitor cell projects to the ambient right unitor on left endpoints. -/
@[simp]
theorem rightUnitor_hom_left {S T : ColaxComma F G} (f : S ⟶ T) :
    (ρ_ f).hom.left = (ρ_ f.left).hom := sorry
/- Proof strategy: unfold the public bicategory instance and project the private comma unitor. -/

/-- The forward right-unitor cell projects to the ambient right unitor on right endpoints. -/
@[simp]
theorem rightUnitor_hom_right {S T : ColaxComma F G} (f : S ⟶ T) :
    (ρ_ f).hom.right = (ρ_ f.right).hom := sorry
/- Proof strategy: unfold the public bicategory instance and project the private comma unitor. -/

/-- The forward associator cell projects to the ambient associator on left endpoints. -/
@[simp]
theorem associator_hom_left {R S T U : ColaxComma F G}
    (f : R ⟶ S) (g : S ⟶ T) (h : T ⟶ U) :
    (α_ f g h).hom.left = (α_ f.left g.left h.left).hom := sorry
/- Proof strategy: unfold the public bicategory instance and project the private comma associator. -/

/-- The forward associator cell projects to the ambient associator on right endpoints. -/
@[simp]
theorem associator_hom_right {R S T U : ColaxComma F G}
    (f : R ⟶ S) (g : S ⟶ T) (h : T ⟶ U) :
    (α_ f g h).hom.right = (α_ f.right g.right h.right).hom := sorry
/- Proof strategy: unfold the public bicategory instance and project the private comma associator. -/

/-- A comma `2`-morphism is invertible when both endpoint `2`-morphisms are invertible. -/
theorem hom₂_isIso [IsLocallyGroupoid A] [IsLocallyGroupoid B]
    {S T : ColaxComma F G} {f g : S ⟶ T} (η : f ⟶ g) : IsIso η := sorry
/- Proof strategy: choose endpoint inverses from local groupoidality, derive their comma
compatibility by cancelling `η.w`, and use `isoMk` with endpoint extensionality. -/

/-- Colax comma bicategories inherit local groupoidality from both endpoint bicategories. -/
instance locallyGroupoid [IsLocallyGroupoid A] [IsLocallyGroupoid B] :
    IsLocallyGroupoid (ColaxComma F G) :=
  fun _ _ ↦ ⟨hom₂_isIso⟩

end ColaxComma
end Bicategory
end CategoryTheory
