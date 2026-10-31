/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import Mathlib.CategoryTheory.Bicategory.InducedBicategory
import Mathlib.Tactic.CrossRefAttribute

/-!
# Isomorphisms in induced bicategories

This leaf exposes the ambient forward and inverse cells of induced-bicategory isomorphisms.
The ambient isomorphism is obtained through mathlib's canonical forgetful pseudofunctor and
`PrelaxFunctor.map₂Iso`; the remaining API records its computations and the `isoMk` readouts.
-/

@[expose] public section

namespace CategoryTheory

open Bicategory
open scoped Bicategory

universe w v u u'

namespace Bicategory.InducedBicategory

variable {B : Type u'} {D : Type u} [Bicategory.{w, v} D] {F : B → D}

namespace Iso

/-- The ambient forward and inverse cells of an induced-bicategory isomorphism satisfy the
first inverse law. -/
theorem toAmbient_hom_inv_id {X Y : InducedBicategory D F} {f g : X ⟶ Y}
    (e : f ≅ g) :
    e.hom.hom ≫ e.inv.hom = 𝟙 f.hom := sorry

/-- The ambient forward and inverse cells of an induced-bicategory isomorphism satisfy the
second inverse law. -/
theorem toAmbient_inv_hom_id {X Y : InducedBicategory D F} {f g : X ⟶ Y}
    (e : f ≅ g) :
    e.inv.hom ≫ e.hom.hom = 𝟙 g.hom := sorry

/-- Forget the induced-bicategory wrapper on a `2`-isomorphism using mathlib's canonical
forgetful pseudofunctor. -/
def toAmbient {X Y : InducedBicategory D F} {f g : X ⟶ Y}
    (e : f ≅ g) : f.hom ≅ g.hom :=
  (Bicategory.InducedBicategory.forget (C := D) (F := F)).toPrelaxFunctor.map₂Iso e

/-- The forward cell of `Iso.toAmbient` is the ambient forward cell. -/
@[simp]
theorem toAmbient_hom {X Y : InducedBicategory D F} {f g : X ⟶ Y}
    (e : f ≅ g) :
    (toAmbient e).hom = e.hom.hom := sorry

/-- The inverse cell of `Iso.toAmbient` is the ambient inverse cell. -/
@[simp]
theorem toAmbient_inv {X Y : InducedBicategory D F} {f g : X ⟶ Y}
    (e : f ≅ g) :
    (toAmbient e).inv = e.inv.hom := sorry

end Iso

namespace IsoMk.Hom

/-- The ambient forward cell of an induced-bicategory isomorphism is the supplied forward
cell. -/
@[simp]
theorem hom {X Y : InducedBicategory D F} {f g : X ⟶ Y}
    (e : f.hom ≅ g.hom) :
    (isoMk e).hom.hom = e.hom := sorry

end IsoMk.Hom

namespace IsoMk.Inv

/-- The ambient inverse cell of an induced-bicategory isomorphism is the supplied inverse
cell. -/
@[simp]
theorem hom {X Y : InducedBicategory D F} {f g : X ⟶ Y}
    (e : f.hom ≅ g.hom) :
    (isoMk e).inv.hom = e.inv := sorry

end IsoMk.Inv

namespace Hom

/-- Forgetting composition in an induced bicategory gives the ambient composite through the
canonical identity isomorphism. This is an explicit data owner, independent of any propositional
equality comparing the two presentations. -/
@[stacks 04Z4 "induced-bicategory composition comparison"]
def compIso {X Y Z : InducedBicategory D F} (f : X ⟶ Y) (g : Y ⟶ Z) :
    f.hom ≫ g.hom ≅ (f ≫ g).hom :=
  Iso.refl _

/-- The forward cell of the induced-bicategory composition comparison is the identity. -/
@[simp, stacks 04Z4 "induced-bicategory composition forward readout"]
theorem compIso.hom {X Y Z : InducedBicategory D F} (f : X ⟶ Y) (g : Y ⟶ Z) :
    (compIso f g).hom = 𝟙 (f.hom ≫ g.hom) := sorry

/-- The inverse cell of the induced-bicategory composition comparison is the identity. -/
@[simp, stacks 04Z4 "induced-bicategory composition inverse readout"]
theorem compIso.inv {X Y Z : InducedBicategory D F} (f : X ⟶ Y) (g : Y ⟶ Z) :
    (compIso f g).inv = 𝟙 ((f ≫ g).hom) := sorry

end Hom

end Bicategory.InducedBicategory

end CategoryTheory
