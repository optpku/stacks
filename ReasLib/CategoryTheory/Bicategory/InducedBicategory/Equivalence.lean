module

public import ReasLib.CategoryTheory.Bicategory.Equivalence.StrictPseudofunctor
public import ReasLib.CategoryTheory.Bicategory.InducedBicategory.Iso
import Mathlib.Tactic.CrossRefAttribute

/-!
# Equivalences in induced bicategories

This module owns the equivalence calculus that depends only on an object map
`F : B → D` and the induced bicategory `InducedBicategory D F`.  Object-property
specializations and local-property instances live in separate focused modules.
-/

@[expose] public section

namespace CategoryTheory

open Bicategory
open scoped Bicategory

universe w v u u'

namespace Bicategory.InducedBicategory

set_option backward.privateInPublic true
set_option backward.privateInPublic.warn false

variable {B : Type u'} {D : Type u} [Bicategory.{w, v} D] {F : B → D}

namespace Implementation.equivalenceMk

/-- The ambient triangle identity remains the triangle identity after lifting an equivalence
to an induced bicategory. -/
private theorem leftTriangle
    {X Y : InducedBicategory D F} (e : F X ≌ F Y) :
    let hom : X ⟶ Y := mkHom e.hom
    let inv : Y ⟶ X := mkHom e.inv
    let unit : 𝟙 X ≅ hom ≫ inv := isoMk e.unit
    let counit : inv ≫ hom ≅ 𝟙 Y := isoMk e.counit
    leftZigzagIso unit counit = λ_ hom ≪≫ (ρ_ hom).symm := sorry

end Implementation.equivalenceMk

/-- Lift an ambient bicategorical equivalence to the bicategory induced along an object map.

The forward and inverse `1`-morphisms and both directions of the unit and counit are retained
literally under `mkHom` and `isoMk`; only their owner changes from `D` to
`InducedBicategory D F`. -/
@[stacks 0040 "lift an ambient equivalence to an induced bicategory"]
def equivalenceMk {X Y : InducedBicategory D F} (e : F X ≌ F Y) : X ≌ Y :=
  let hom : X ⟶ Y := mkHom e.hom
  let inv : Y ⟶ X := mkHom e.inv
  let unit : 𝟙 X ≅ hom ≫ inv := isoMk e.unit
  let counit : inv ≫ hom ≅ 𝟙 Y := isoMk e.counit
  {
    hom := hom
    inv := inv
    unit := unit
    counit := counit
    left_triangle := Implementation.equivalenceMk.leftTriangle e
  }

/-- The ambient forward morphism of a lifted induced-bicategory equivalence is the supplied
forward morphism. -/
@[simp]
theorem equivalenceMk.hom.toAmbient
    {X Y : InducedBicategory D F} (e : F X ≌ F Y) :
    (equivalenceMk e).hom.hom = e.hom := sorry

/-- The ambient inverse morphism of a lifted induced-bicategory equivalence is the supplied
inverse morphism. -/
@[simp]
theorem equivalenceMk.inv.toAmbient
    {X Y : InducedBicategory D F} (e : F X ≌ F Y) :
    (equivalenceMk e).inv.hom = e.inv := sorry

/-- The ambient forward unit cell of a lifted induced-bicategory equivalence is the supplied
unit cell. -/
@[simp]
theorem equivalenceMk.unit.hom.toAmbient
    {X Y : InducedBicategory D F} (e : F X ≌ F Y) :
    (equivalenceMk e).unit.hom.hom = e.unit.hom := sorry

/-- The ambient inverse unit cell of a lifted induced-bicategory equivalence is the supplied
inverse unit cell. -/
@[simp]
theorem equivalenceMk.unit.inv.toAmbient
    {X Y : InducedBicategory D F} (e : F X ≌ F Y) :
    (equivalenceMk e).unit.inv.hom = e.unit.inv := sorry

/-- The ambient forward counit cell of a lifted induced-bicategory equivalence is the supplied
counit cell. -/
@[simp]
theorem equivalenceMk.counit.hom.toAmbient
    {X Y : InducedBicategory D F} (e : F X ≌ F Y) :
    (equivalenceMk e).counit.hom.hom = e.counit.hom := sorry

/-- The ambient inverse counit cell of a lifted induced-bicategory equivalence is the supplied
inverse counit cell. -/
@[simp]
theorem equivalenceMk.counit.inv.toAmbient
    {X Y : InducedBicategory D F} (e : F X ≌ F Y) :
    (equivalenceMk e).counit.inv.hom = e.counit.inv := sorry

/-- Forgetting a lifted induced-bicategory equivalence recovers the supplied ambient
equivalence. -/
@[simp]
theorem equivalenceMk.mapEquivalence
    {X Y : InducedBicategory D F} (e : F X ≌ F Y) :
    forget.mapEquivalence (equivalenceMk e) = e := sorry

/-- Lifting the ambient image of an induced-bicategory equivalence recovers the original
equivalence. -/
@[simp]
theorem equivalenceMk.ofMapEquivalence
    {X Y : InducedBicategory D F} (e : X ≌ Y) :
    equivalenceMk (forget.mapEquivalence e) = e := sorry

/-- Equivalences in an induced bicategory are canonically the ambient equivalences between the
corresponding object images. -/
@[stacks 0040 "equivalences in an induced bicategory and ambient equivalences"]
def equivalenceEquiv (X Y : InducedBicategory D F) :
    (X ≌ Y) ≃ (F X ≌ F Y) where
  toFun e := forget.mapEquivalence e
  invFun := equivalenceMk
  left_inv := equivalenceMk.ofMapEquivalence
  right_inv := equivalenceMk.mapEquivalence

/-- The forward map of `equivalenceEquiv` forgets the induced-bicategory owner. -/
@[simp]
theorem equivalenceEquiv.apply
    {X Y : InducedBicategory D F} (e : X ≌ Y) :
    equivalenceEquiv X Y e = forget.mapEquivalence e := sorry

/-- The inverse map of `equivalenceEquiv` lifts an ambient equivalence. -/
@[simp]
theorem equivalenceEquiv.symm_apply
    {X Y : InducedBicategory D F} (e : F X ≌ F Y) :
    (equivalenceEquiv X Y).symm e = equivalenceMk e := sorry

/-- Lifting the ambient identity equivalence gives the identity induced-bicategory
equivalence. -/
@[simp]
theorem equivalenceMk.id (X : InducedBicategory D F) :
    equivalenceMk (Bicategory.Equivalence.id (F X)) =
      Bicategory.Equivalence.id X := sorry

/-- Lifting an ambient equivalence commutes with reversing it. -/
@[simp]
theorem equivalenceMk.symm
    {X Y : InducedBicategory D F} (e : F X ≌ F Y) :
    equivalenceMk e.symm = (equivalenceMk e).symm := sorry

/-- Lifting ambient equivalences commutes with their composition. -/
@[simp]
theorem equivalenceMk.trans
    {X Y Z : InducedBicategory D F}
    (e : F X ≌ F Y) (e' : F Y ≌ F Z) :
    equivalenceMk (e.trans e') =
      (equivalenceMk e).trans (equivalenceMk e') := sorry

/- Data audit (mathlib 4.32): `equivalenceMk` retains the ambient forward and inverse
`1`-morphisms and all four unit/counit cells explicitly under the induced wrappers.
`equivalenceEquiv` has explicit mutually inverse functions. Any `sorryAx` is confined to the
triangle law and equality proofs; no ambient equivalence datum is chosen or reconstructed. -/

end Bicategory.InducedBicategory

end CategoryTheory
