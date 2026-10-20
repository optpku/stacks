/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.CategoryTheory.Bicategory.LocallyInduced.Lift
public import ReasLib.CategoryTheory.Bicategory.LocallyInduced.Iso
public import ReasLib.CategoryTheory.Bicategory.HomProperty.Equivalence
public import ReasLib.CategoryTheory.Bicategory.Equivalence.StrictPseudofunctor
import Mathlib.Tactic.CrossRefAttribute

/-!
# Equivalences in locally induced bicategories

This file lifts ambient bicategorical equivalences when both underlying `1`-morphisms satisfy
the selected hom property, together with computation lemmas for the retained ambient data.
-/

@[expose] public section

namespace CategoryTheory

open Bicategory
open ObjectProperty
open scoped Bicategory

universe w v u u'

namespace Bicategory

variable {B : Type u'}

namespace LocallyInducedBicategory

set_option backward.privateInPublic true
set_option backward.privateInPublic.warn false

variable {C : Type u} [Bicategory.{w, v} C] {F : B → C}
  {Q : HomProperty F} [Q.IsMultiplicative]

namespace Implementation.equivalenceMk

/-- The ambient triangle identity remains the triangle identity after lifting the two
`1`-morphisms and the unit and counit to a locally induced bicategory. -/
private theorem leftTriangle
    {X Y : LocallyInducedBicategory C F Q}
    (e : F X ≌ F Y) (hom_mem : Q X Y e.hom) (inv_mem : Q Y X e.inv) :
    let hom : X ⟶ Y := mkHom e.hom hom_mem
    let inv : Y ⟶ X := mkHom e.inv inv_mem
    let unit : 𝟙 X ≅ hom ≫ inv := (Q X X).isoMk e.unit
    let counit : inv ≫ hom ≅ 𝟙 Y := (Q Y Y).isoMk e.counit
    leftZigzagIso unit counit = λ_ hom ≪≫ (ρ_ hom).symm := sorry

end Implementation.equivalenceMk

/-- Lift an ambient bicategorical equivalence whose forward and inverse `1`-morphisms satisfy
the selected hom property to an equivalence in the locally induced bicategory. Local fullness
supplies the unit and counit `2`-isomorphisms without any additional hypotheses. The lift
retains the supplied ambient unit and counit rather than adjointifying either of them again. -/
@[stacks 0040 "lift an admissible ambient equivalence to a locally induced bicategory"]
def equivalenceMk
    {X Y : LocallyInducedBicategory C F Q}
    (e : F X ≌ F Y) (hom_mem : Q X Y e.hom) (inv_mem : Q Y X e.inv) :
    X ≌ Y where
    hom := mkHom e.hom hom_mem
    inv := mkHom e.inv inv_mem
    unit := (Q X X).isoMk e.unit
    counit := (Q Y Y).isoMk e.counit
    left_triangle := Implementation.equivalenceMk.leftTriangle e hom_mem inv_mem

/-- The unit of a lifted locally induced equivalence is the ambient unit regarded in the selected
hom category. -/
@[simp]
theorem equivalenceMk.unit
    {X Y : LocallyInducedBicategory C F Q}
    (e : F X ≌ F Y) (hom_mem : Q X Y e.hom) (inv_mem : Q Y X e.inv) :
    (equivalenceMk e hom_mem inv_mem).unit = (Q X X).isoMk e.unit := sorry

/-- The forward selected `2`-cell of a lifted equivalence unit is the forward cell of the
ambient unit, lifted by `isoMk`. -/
@[simp]
theorem equivalenceMk.unit.hom
    {X Y : LocallyInducedBicategory C F Q}
    (e : F X ≌ F Y) (hom_mem : Q X Y e.hom) (inv_mem : Q Y X e.inv) :
    (equivalenceMk e hom_mem inv_mem).unit.hom = ((Q X X).isoMk e.unit).hom := sorry

/-- The inverse selected `2`-cell of a lifted equivalence unit is the inverse cell of the ambient
unit, lifted by `isoMk`. -/
@[simp]
theorem equivalenceMk.unit.inv
    {X Y : LocallyInducedBicategory C F Q}
    (e : F X ≌ F Y) (hom_mem : Q X Y e.hom) (inv_mem : Q Y X e.inv) :
    (equivalenceMk e hom_mem inv_mem).unit.inv = ((Q X X).isoMk e.unit).inv := sorry

/-- The counit of a lifted locally induced equivalence is the ambient counit regarded in the
selected hom category. -/
@[simp]
theorem equivalenceMk.counit
    {X Y : LocallyInducedBicategory C F Q}
    (e : F X ≌ F Y) (hom_mem : Q X Y e.hom) (inv_mem : Q Y X e.inv) :
    (equivalenceMk e hom_mem inv_mem).counit = (Q Y Y).isoMk e.counit := sorry

/-- The forward selected `2`-cell of a lifted equivalence counit is the forward cell of the
ambient counit, lifted by `isoMk`. -/
@[simp]
theorem equivalenceMk.counit.hom
    {X Y : LocallyInducedBicategory C F Q}
    (e : F X ≌ F Y) (hom_mem : Q X Y e.hom) (inv_mem : Q Y X e.inv) :
    (equivalenceMk e hom_mem inv_mem).counit.hom = ((Q Y Y).isoMk e.counit).hom := sorry

/-- The inverse selected `2`-cell of a lifted equivalence counit is the inverse cell of the ambient
counit, lifted by `isoMk`. -/
@[simp]
theorem equivalenceMk.counit.inv
    {X Y : LocallyInducedBicategory C F Q}
    (e : F X ≌ F Y) (hom_mem : Q X Y e.hom) (inv_mem : Q Y X e.inv) :
    (equivalenceMk e hom_mem inv_mem).counit.inv = ((Q Y Y).isoMk e.counit).inv := sorry

/-- Forget a locally induced equivalence to its ambient equivalence. -/
@[stacks 0040 "ambient equivalence underlying a locally induced equivalence"]
def ambientEquivalence
    {X Y : LocallyInducedBicategory C F Q} (e : X ≌ Y) :
    F X ≌ F Y :=
  (forget C F Q).mapEquivalence e

/-- The ambient forward `1`-morphism of a lifted locally induced equivalence is the supplied
forward `1`-morphism. -/
@[simp]
theorem equivalenceMk.hom.toAmbient
    {X Y : LocallyInducedBicategory C F Q}
    (e : F X ≌ F Y) (hom_mem : Q X Y e.hom) (inv_mem : Q Y X e.inv) :
    (equivalenceMk e hom_mem inv_mem).hom.obj = e.hom := sorry

/-- The ambient inverse `1`-morphism of a lifted locally induced equivalence is the supplied
inverse `1`-morphism. -/
@[simp]
theorem equivalenceMk.inv.toAmbient
    {X Y : LocallyInducedBicategory C F Q}
    (e : F X ≌ F Y) (hom_mem : Q X Y e.hom) (inv_mem : Q Y X e.inv) :
    (equivalenceMk e hom_mem inv_mem).inv.obj = e.inv := sorry

/-- The ambient forward unit cell of a lifted locally induced equivalence is the supplied
ambient forward unit cell. -/
@[simp]
theorem equivalenceMk.unit.hom.toAmbient
    {X Y : LocallyInducedBicategory C F Q}
    (e : F X ≌ F Y) (hom_mem : Q X Y e.hom) (inv_mem : Q Y X e.inv) :
    (LocallyInducedBicategory.Iso.toAmbient
      (equivalenceMk e hom_mem inv_mem).unit).hom =
      e.unit.hom := sorry

/-- The ambient inverse unit cell of a lifted locally induced equivalence is the supplied
ambient inverse unit cell. -/
@[simp]
theorem equivalenceMk.unit.inv.toAmbient
    {X Y : LocallyInducedBicategory C F Q}
    (e : F X ≌ F Y) (hom_mem : Q X Y e.hom) (inv_mem : Q Y X e.inv) :
    (LocallyInducedBicategory.Iso.toAmbient
      (equivalenceMk e hom_mem inv_mem).unit).inv =
      e.unit.inv := sorry

/-- The ambient forward counit cell of a lifted locally induced equivalence is the supplied
ambient forward counit cell. -/
@[simp]
theorem equivalenceMk.counit.hom.toAmbient
    {X Y : LocallyInducedBicategory C F Q}
    (e : F X ≌ F Y) (hom_mem : Q X Y e.hom) (inv_mem : Q Y X e.inv) :
    (LocallyInducedBicategory.Iso.toAmbient
      (equivalenceMk e hom_mem inv_mem).counit).hom =
      e.counit.hom := sorry

/-- The ambient inverse counit cell of a lifted locally induced equivalence is the supplied
inverse counit cell. -/
@[simp]
theorem equivalenceMk.counit.inv.toAmbient
    {X Y : LocallyInducedBicategory C F Q}
    (e : F X ≌ F Y) (hom_mem : Q X Y e.hom) (inv_mem : Q Y X e.inv) :
    (LocallyInducedBicategory.Iso.toAmbient
      (equivalenceMk e hom_mem inv_mem).counit).inv =
      e.counit.inv := sorry

/-- The ambient forward morphism of a forgotten locally induced equivalence is its underlying
forward morphism. -/
@[simp]
theorem ambientEquivalence.hom
    {X Y : LocallyInducedBicategory C F Q} (e : X ≌ Y) :
    (ambientEquivalence e).hom = e.hom.obj := sorry

/-- The ambient inverse morphism of a forgotten locally induced equivalence is its underlying
inverse morphism. -/
@[simp]
theorem ambientEquivalence.inv
    {X Y : LocallyInducedBicategory C F Q} (e : X ≌ Y) :
    (ambientEquivalence e).inv = e.inv.obj := sorry

/-- The forward morphism of the ambient equivalence underlying a locally induced equivalence
satisfies the selected hom property. -/
theorem ambientEquivalence.hom_mem
    {X Y : LocallyInducedBicategory C F Q} (e : X ≌ Y) :
    Q X Y (ambientEquivalence e).hom := sorry

/-- The inverse morphism of the ambient equivalence underlying a locally induced equivalence
satisfies the selected hom property. -/
theorem ambientEquivalence.inv_mem
    {X Y : LocallyInducedBicategory C F Q} (e : X ≌ Y) :
    Q Y X (ambientEquivalence e).inv := sorry

/-- Forgetting a lifted admissible ambient equivalence recovers the supplied equivalence. -/
@[simp]
theorem ambientEquivalence.equivalenceMk
    {X Y : LocallyInducedBicategory C F Q}
    (e : F X ≌ F Y) (hom_mem : Q X Y e.hom) (inv_mem : Q Y X e.inv) :
    ambientEquivalence (equivalenceMk e hom_mem inv_mem) = e := sorry

/-- Lifting the ambient equivalence underlying a locally induced equivalence with its stored
membership witnesses recovers the original equivalence. -/
@[simp]
theorem equivalenceMk.ambientEquivalence
    {X Y : LocallyInducedBicategory C F Q} (e : X ≌ Y) :
    equivalenceMk (ambientEquivalence e)
      (ambientEquivalence.hom_mem e) (ambientEquivalence.inv_mem e) = e := sorry

/-- Equivalences in a locally induced bicategory are canonically ambient equivalences whose
forward and inverse `1`-morphisms satisfy the selected hom property. -/
@[stacks 0040 "locally induced equivalences and admissible ambient equivalences"]
def equivalenceEquiv (X Y : LocallyInducedBicategory C F Q) :
    (X ≌ Y) ≃ Q.AdmissibleEquivalence X Y where
  toFun e := HomProperty.AdmissibleEquivalence.mk (ambientEquivalence e)
    (ambientEquivalence.hom_mem e) (ambientEquivalence.inv_mem e)
  invFun e := equivalenceMk e.toEquivalence e.hom_mem e.inv_mem
  left_inv := equivalenceMk.ambientEquivalence
  right_inv := sorry

/-- The forward map of `equivalenceEquiv` retains the ambient equivalence and its stored
admissibility witnesses. -/
@[simp]
theorem equivalenceEquiv.apply
    {X Y : LocallyInducedBicategory C F Q} (e : X ≌ Y) :
    equivalenceEquiv X Y e =
      HomProperty.AdmissibleEquivalence.mk (ambientEquivalence e)
        (ambientEquivalence.hom_mem e) (ambientEquivalence.inv_mem e) := sorry

/-- The inverse map of `equivalenceEquiv` lifts the supplied admissible ambient equivalence. -/
@[simp]
theorem equivalenceEquiv.symm_apply
    {X Y : LocallyInducedBicategory C F Q}
    (e : Q.AdmissibleEquivalence X Y) :
    (equivalenceEquiv X Y).symm e =
      equivalenceMk e.toEquivalence e.hom_mem e.inv_mem := sorry

/- Data and axiom audit (mathlib 4.32): `equivalenceMk` retains the supplied ambient
equivalence and adds only the two necessary hom-membership witnesses. `ambientEquivalence`
uses the canonical forgetful pseudofunctor. The two roundtrip statements show that neither
direction introduces a second choice of inverse, unit, or counit. -/

end LocallyInducedBicategory

end Bicategory

end CategoryTheory
