/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import ReasLib.CategoryTheory.Bicategory.LocallyInduced.Morphisms
import Mathlib.Tactic.CrossRefAttribute

/-!
# Ambient isomorphisms for locally induced homs

The locally induced bicategory keeps all ambient `2`-cells between selected `1`-morphisms, but a
hom-category is still represented by a full-subcategory wrapper.  This leaf owns the canonical
projection from an isomorphism in that hom-category to its ambient isomorphism.
-/

@[expose] public section

namespace CategoryTheory.Bicategory.LocallyInducedBicategory

open CategoryTheory
open scoped CategoryTheory.Bicategory

universe w v u u'

variable {B : Type u'}
variable {C : Type u} [Bicategory.{w, v} C]
variable {F : B → C} {Q : HomProperty F} [Q.IsMultiplicative]

/-- Build a locally induced 2-isomorphism from an ambient 2-isomorphism. -/
def isoMk {X Y : LocallyInducedBicategory C F Q} {f g : X ⟶ Y}
    (e : f.obj ≅ g.obj) : f ≅ g :=
  (Q _ _).isoMk e

namespace Iso

/-- Forget the locally induced hom wrapper on a `2`-isomorphism. -/
def toAmbient {X Y : LocallyInducedBicategory C F Q} {f g : X ⟶ Y}
    (e : f ≅ g) : f.obj ≅ g.obj where
  hom := e.hom.hom
  inv := e.inv.hom
  hom_inv_id := sorry
  inv_hom_id := sorry

/-- The ambient forward cell of a locally induced `2`-isomorphism. -/
@[simp]
theorem toAmbient_hom {X Y : LocallyInducedBicategory C F Q} {f g : X ⟶ Y}
    (e : f ≅ g) :
    (toAmbient e).hom = e.hom.hom := rfl

/-- The ambient inverse cell of a locally induced `2`-isomorphism. -/
@[simp]
theorem toAmbient_inv {X Y : LocallyInducedBicategory C F Q} {f g : X ⟶ Y}
    (e : f ≅ g) :
    (toAmbient e).inv = e.inv.hom := rfl

/-- Forgetting the identity `2`-isomorphism gives the ambient identity isomorphism. -/
@[simp]
theorem toAmbient_refl {X Y : LocallyInducedBicategory C F Q} (f : X ⟶ Y) :
    toAmbient (CategoryTheory.Iso.refl f) = CategoryTheory.Iso.refl f.obj := sorry

/-- Forgetting commutes with symmetry of locally induced `2`-isomorphisms. -/
@[simp]
theorem toAmbient_symm {X Y : LocallyInducedBicategory C F Q} {f g : X ⟶ Y}
    (e : f ≅ g) :
    toAmbient e.symm = (toAmbient e).symm := sorry

/-- Forgetting commutes with transitivity of locally induced `2`-isomorphisms. -/
@[simp]
theorem toAmbient_trans {X Y : LocallyInducedBicategory C F Q} {f g h : X ⟶ Y}
    (e : f ≅ g) (e' : g ≅ h) :
    toAmbient (e ≪≫ e') = toAmbient e ≪≫ toAmbient e' := sorry

/-- The ambient projection is injective on locally induced `2`-isomorphisms. -/
theorem toAmbient_injective {X Y : LocallyInducedBicategory C F Q} {f g : X ⟶ Y} :
    Function.Injective (toAmbient : (f ≅ g) → (f.obj ≅ g.obj)) := sorry

/-- Locally induced `2`-isomorphisms are equal when their ambient forward cells are equal. -/
@[ext]
theorem ext {X Y : LocallyInducedBicategory C F Q} {f g : X ⟶ Y} {e e' : f ≅ g}
    (h : (toAmbient e).hom = (toAmbient e').hom) :
    e = e' := sorry

end Iso

/-- The ambient forward cell of a locally induced left unitor is the ambient left unitor. -/
@[simp]
theorem leftUnitor.toAmbient.hom
    {X Y : LocallyInducedBicategory C F Q} (f : X ⟶ Y) :
    (Iso.toAmbient (λ_ f)).hom = (λ_ f.obj).hom := sorry

/-- The ambient inverse cell of a locally induced left unitor is the ambient inverse left unitor. -/
@[simp]
theorem leftUnitor.toAmbient.inv
    {X Y : LocallyInducedBicategory C F Q} (f : X ⟶ Y) :
    (Iso.toAmbient (λ_ f)).inv = (λ_ f.obj).inv := sorry

/-- The ambient forward cell of a locally induced right unitor is the ambient right unitor. -/
@[simp]
theorem rightUnitor.toAmbient.hom
    {X Y : LocallyInducedBicategory C F Q} (f : X ⟶ Y) :
    (Iso.toAmbient (ρ_ f)).hom = (ρ_ f.obj).hom := sorry

/-- The ambient inverse cell of a locally induced right unitor is the ambient inverse right unitor. -/
@[simp]
theorem rightUnitor.toAmbient.inv
    {X Y : LocallyInducedBicategory C F Q} (f : X ⟶ Y) :
    (Iso.toAmbient (ρ_ f)).inv = (ρ_ f.obj).inv := sorry

/-- The ambient forward cell of a locally induced associator is the ambient associator. -/
@[simp]
theorem associator.toAmbient.hom {W X Y Z : LocallyInducedBicategory C F Q}
    (f : W ⟶ X) (g : X ⟶ Y) (h : Y ⟶ Z) :
    (Iso.toAmbient (α_ f g h)).hom = (α_ f.obj g.obj h.obj).hom := sorry

/-- The ambient inverse cell of a locally induced associator is the ambient inverse associator. -/
@[simp]
theorem associator.toAmbient.inv {W X Y Z : LocallyInducedBicategory C F Q}
    (f : W ⟶ X) (g : X ⟶ Y) (h : Y ⟶ Z) :
    (Iso.toAmbient (α_ f g h)).inv = (α_ f.obj g.obj h.obj).inv := sorry

/-- The ambient forward cell of isoMk is the supplied ambient forward cell. -/
@[simp]
theorem isoMk.toAmbient.hom {X Y : LocallyInducedBicategory C F Q} {f g : X ⟶ Y}
    (e : f.obj ≅ g.obj) :
    (Iso.toAmbient (isoMk e)).hom = e.hom := sorry

/-- The ambient inverse cell of isoMk is the supplied ambient inverse cell. -/
@[simp]
theorem isoMk.toAmbient.inv {X Y : LocallyInducedBicategory C F Q} {f g : X ⟶ Y}
    (e : f.obj ≅ g.obj) :
    (Iso.toAmbient (isoMk e)).inv = e.inv := sorry

end CategoryTheory.Bicategory.LocallyInducedBicategory
