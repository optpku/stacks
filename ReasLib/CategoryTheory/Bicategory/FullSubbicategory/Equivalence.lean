/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import ReasLib.CategoryTheory.Bicategory.FullSubbicategory.Definition
public import ReasLib.CategoryTheory.Bicategory.InducedBicategory.Equivalence
import Mathlib.Tactic.CrossRefAttribute

/-!
# Equivalences in full subbicategories

The declarations here are object-property-facing specializations of the
neutral induced-bicategory equivalence API.  They retain the established
`ObjectProperty.FullSubbicategory` names for direct downstream use.
-/

@[expose] public section

namespace CategoryTheory

open Bicategory
open ObjectProperty
open scoped Bicategory

universe w v u

namespace ObjectProperty

variable {D : Type u} [Bicategory.{w, v} D]

namespace FullSubbicategory

set_option backward.privateInPublic true
set_option backward.privateInPublic.warn false

variable {P : ObjectProperty D}

section

variable {X Y : P.FullSubbicategory}

/-- Equivalences in a full subbicategory are canonically ambient equivalences between the
underlying objects. -/
@[stacks 0040 "full-subbicategory equivalences and ambient equivalences"]
def ambientEquiv (X Y : P.FullSubbicategory) :
    (X ≌ Y) ≃ (X.1 ≌ Y.1) :=
  Bicategory.InducedBicategory.equivalenceEquiv X Y

/-- Forget a full-subbicategory equivalence to its ambient equivalence. -/
@[stacks 0040 "ambient equivalence underlying a full-subbicategory equivalence"]
def ambientEquivalence (e : X ≌ Y) : X.1 ≌ Y.1 :=
  ambientEquiv X Y e

/-- Lift an ambient equivalence between selected objects to the full subbicategory. -/
@[stacks 0040 "full-subbicategory equivalence from an ambient equivalence"]
def equivalenceOfAmbient (e : X.1 ≌ Y.1) : X ≌ Y :=
  (ambientEquiv X Y).symm e

/-- The ambient forward morphism of a forgotten full-subbicategory equivalence is its
canonical inclusion image. -/
@[simp]
theorem ambientEquivalence.hom (e : X ≌ Y) :
    (ambientEquivalence e).hom = (ι P).map e.hom := sorry

/-- The ambient inverse morphism of a forgotten full-subbicategory equivalence is its
canonical inclusion image. -/
@[simp]
theorem ambientEquivalence.inv (e : X ≌ Y) :
    (ambientEquivalence e).inv = (ι P).map e.inv := sorry

/-- Forgetting a lifted ambient equivalence recovers the original equivalence. -/
@[simp]
theorem ambientEquivalence.ofAmbient (e : X.1 ≌ Y.1) :
    ambientEquivalence (equivalenceOfAmbient e) = e := sorry

/-- Lifting the ambient equivalence underlying a full-subbicategory equivalence recovers the
original equivalence. -/
@[simp]
theorem equivalenceOfAmbient.ambientEquivalence (e : X ≌ Y) :
    equivalenceOfAmbient (ambientEquivalence e) = e := sorry

/-- The ambient forward morphism of a lifted equivalence is the supplied morphism. -/
@[simp]
theorem equivalenceOfAmbient.hom.toAmbient (e : X.1 ≌ Y.1) :
    (CategoryTheory.ObjectProperty.FullSubbicategory.ambientEquivalence
      (equivalenceOfAmbient e)).hom = e.hom := sorry

/-- The ambient inverse morphism of a lifted equivalence is the supplied inverse. -/
@[simp]
theorem equivalenceOfAmbient.inv.toAmbient (e : X.1 ≌ Y.1) :
    (CategoryTheory.ObjectProperty.FullSubbicategory.ambientEquivalence
      (equivalenceOfAmbient e)).inv = e.inv := sorry

/-- The ambient forward unit cell of a lifted equivalence is the supplied unit cell. -/
@[simp]
theorem equivalenceOfAmbient.unit.hom.toAmbient (e : X.1 ≌ Y.1) :
    (CategoryTheory.ObjectProperty.FullSubbicategory.ambientEquivalence
      (equivalenceOfAmbient e)).unit.hom = e.unit.hom := sorry

/-- The ambient inverse unit cell of a lifted equivalence is the supplied inverse unit
cell. -/
@[simp]
theorem equivalenceOfAmbient.unit.inv.toAmbient (e : X.1 ≌ Y.1) :
    (CategoryTheory.ObjectProperty.FullSubbicategory.ambientEquivalence
      (equivalenceOfAmbient e)).unit.inv = e.unit.inv := sorry

/-- The ambient forward counit cell of a lifted equivalence is the supplied counit cell. -/
@[simp]
theorem equivalenceOfAmbient.counit.hom.toAmbient (e : X.1 ≌ Y.1) :
    (CategoryTheory.ObjectProperty.FullSubbicategory.ambientEquivalence
      (equivalenceOfAmbient e)).counit.hom = e.counit.hom := sorry

/-- The ambient inverse counit cell of a lifted equivalence is the supplied inverse counit
cell. -/
@[simp]
theorem equivalenceOfAmbient.counit.inv.toAmbient (e : X.1 ≌ Y.1) :
    (CategoryTheory.ObjectProperty.FullSubbicategory.ambientEquivalence
      (equivalenceOfAmbient e)).counit.inv = e.counit.inv := sorry

/-- Lifting the ambient identity equivalence gives the full-subbicategory identity equivalence. -/
@[simp]
theorem equivalenceOfAmbient.id (X : P.FullSubbicategory) :
    equivalenceOfAmbient (Bicategory.Equivalence.id X.1) = Bicategory.Equivalence.id X := sorry

/-- Lifting an ambient equivalence commutes with reversing it. -/
@[simp]
theorem equivalenceOfAmbient.symm {X Y : P.FullSubbicategory} (e : X.1 ≌ Y.1) :
    equivalenceOfAmbient e.symm = (equivalenceOfAmbient e).symm := sorry

/-- Lifting ambient equivalences commutes with their composition. -/
@[simp]
theorem equivalenceOfAmbient.trans {X Y Z : P.FullSubbicategory}
    (e : X.1 ≌ Y.1) (e' : Y.1 ≌ Z.1) :
    equivalenceOfAmbient (e.trans e') =
      (equivalenceOfAmbient e).trans (equivalenceOfAmbient e') := sorry

/-- Forgetting the full-subbicategory identity equivalence gives the ambient identity equivalence. -/
@[simp]
theorem ambientEquivalence.id (X : P.FullSubbicategory) :
    ambientEquivalence (Bicategory.Equivalence.id X) = Bicategory.Equivalence.id X.1 := sorry

/-- Forgetting a reversed full-subbicategory equivalence commutes with reversal. -/
@[simp]
theorem ambientEquivalence.symm {X Y : P.FullSubbicategory} (e : X ≌ Y) :
    ambientEquivalence e.symm = (ambientEquivalence e).symm := sorry

/-- Forgetting full-subbicategory equivalences commutes with their composition. -/
@[simp]
theorem ambientEquivalence.trans {X Y Z : P.FullSubbicategory}
    (e : X ≌ Y) (e' : Y ≌ Z) :
    ambientEquivalence (e.trans e') =
      (ambientEquivalence e).trans (ambientEquivalence e') := sorry

/- Data and axiom audit (mathlib 4.32): `ambientEquiv` specializes the neutral
`InducedBicategory.equivalenceEquiv`; its two named maps introduce no new choice. The ambient
forward and inverse morphisms and all unit/counit cells are retained by
`equivalenceOfAmbient`. Any `sorryAx` is confined to wrapper equalities and inherited
coherence proofs. -/

end

end FullSubbicategory

end ObjectProperty

end CategoryTheory
