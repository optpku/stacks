module

public import ReasLib.CategoryTheory.Bicategory.InducedBicategory.Equivalence
public import ReasLib.CategoryTheory.Bicategory.Limits.Cospan.Bundled.Modification
import Mathlib.Tactic.CrossRefAttribute

/-!
# Equivalences of bundled bicategorical cospans

The bicategory of bundled cospans is induced from the bicategory of walking-cospan
pseudofunctors. Consequently an equivalence of bundled cospans is canonically the same datum
as an equivalence of their diagrams. This file specializes the neutral
`Bicategory.InducedBicategory.equivalenceEquiv` API and exposes both directions with their
wrapper computations.

Endpoint projections and componentwise constructors are layered separately.
-/

@[expose] public section

set_option backward.privateInPublic true
set_option backward.privateInPublic.warn false

open scoped CategoryTheory.Bicategory CategoryTheory.Pseudofunctor.StrongTrans

universe w v u

namespace CategoryTheory.Bicategory.Cospan

variable {B : Type u} [Bicategory.{w, v} B]
variable {S T : Cospan B}

/-- Equivalences of bundled cospans are canonically equivalences of their walking-cospan
diagrams.

This is the specialization of `Bicategory.InducedBicategory.equivalenceEquiv` to
`Cospan.diagram`. -/
@[stacks 0040 "equivalences of bundled cospans and their diagrams"]
def diagramEquiv (S T : Cospan B) :
    (S ≌ T) ≃ (S.diagram ≌ T.diagram) :=
  Bicategory.InducedBicategory.equivalenceEquiv
    (F := fun R : Cospan B ↦ R.diagram) S T

/-- Forget a bundled-cospan equivalence to an equivalence of its walking-cospan diagrams. -/
@[stacks 0040 "diagram equivalence underlying a bundled-cospan equivalence"]
def diagramEquivalence (e : S ≌ T) : S.diagram ≌ T.diagram :=
  diagramEquiv S T e

/-- Lift an equivalence of walking-cospan diagrams to an equivalence of bundled cospans. -/
@[stacks 0040 "bundled-cospan equivalence from a diagram equivalence"]
def equivalenceOfDiagram (e : S.diagram ≌ T.diagram) : S ≌ T :=
  (diagramEquiv S T).symm e

/-- The forward strong transformation of a forgotten bundled-cospan equivalence is the
underlying cospan transformation of its forward morphism. -/
@[simp]
theorem diagramEquivalence.hom (e : S ≌ T) :
    (diagramEquivalence e).hom = Hom.toCospanTransform e.hom := sorry

/-- The inverse strong transformation of a forgotten bundled-cospan equivalence is the
underlying cospan transformation of its inverse morphism. -/
@[simp]
theorem diagramEquivalence.inv (e : S ≌ T) :
    (diagramEquivalence e).inv = Hom.toCospanTransform e.inv := sorry

/-- Forgetting a lifted diagram equivalence recovers the original diagram equivalence. -/
@[simp]
theorem diagramEquivalence.ofDiagram
    (e : S.diagram ≌ T.diagram) :
    diagramEquivalence (equivalenceOfDiagram e) = e := sorry

/-- Lifting the diagram equivalence underlying a bundled equivalence recovers the bundled
equivalence. -/
@[simp]
theorem equivalenceOfDiagram.diagramEquivalence (e : S ≌ T) :
    equivalenceOfDiagram (diagramEquivalence e) = e := sorry

/-- The underlying forward transformation of a lifted diagram equivalence is the supplied
forward transformation. -/
@[simp]
theorem equivalenceOfDiagram.hom.toCospanTransform
    (e : S.diagram ≌ T.diagram) :
    (equivalenceOfDiagram e).hom.hom = e.hom := sorry

/-- The underlying inverse transformation of a lifted diagram equivalence is the supplied
inverse transformation. -/
@[simp]
theorem equivalenceOfDiagram.inv.toCospanTransform
    (e : S.diagram ≌ T.diagram) :
    (equivalenceOfDiagram e).inv.hom = e.inv := sorry

/-- The underlying forward unit modification of a lifted diagram equivalence is the supplied
forward unit modification. -/
@[simp]
theorem equivalenceOfDiagram.unit.hom.toModification
    (e : S.diagram ≌ T.diagram) :
    (equivalenceOfDiagram e).unit.hom.hom = e.unit.hom := sorry

/-- The underlying inverse unit modification of a lifted diagram equivalence is the supplied
inverse unit modification. -/
@[simp]
theorem equivalenceOfDiagram.unit.inv.toModification
    (e : S.diagram ≌ T.diagram) :
    (equivalenceOfDiagram e).unit.inv.hom = e.unit.inv := sorry

/-- The underlying forward counit modification of a lifted diagram equivalence is the
supplied forward counit modification. -/
@[simp]
theorem equivalenceOfDiagram.counit.hom.toModification
    (e : S.diagram ≌ T.diagram) :
    (equivalenceOfDiagram e).counit.hom.hom = e.counit.hom := sorry

/-- The underlying inverse counit modification of a lifted diagram equivalence is the
supplied inverse counit modification. -/
@[simp]
theorem equivalenceOfDiagram.counit.inv.toModification
    (e : S.diagram ≌ T.diagram) :
    (equivalenceOfDiagram e).counit.inv.hom = e.counit.inv := sorry

/- Data and axiom audit (mathlib 4.32):

`diagramEquiv` is a direct specialization of the neutral induced-bicategory owner;
`diagramEquivalence` and `equivalenceOfDiagram` are its two maps. Thus all forward, inverse,
unit, and counit data are inherited without a second choice. `#print axioms` reports
`[propext, sorryAx, Classical.choice, Quot.sound]`; `sorryAx` is confined to the generic
triangle/coherence and wrapper-equality proofs. -/

end CategoryTheory.Bicategory.Cospan
