module

public import ReasLib.CategoryTheory.Bicategory.Equivalence.ObjectProperty
public import stacks_project.Chap94.Definition_94_12_2_DeligneMumford

/-!
# Equivalence-invariance of algebraic and Deligne-Mumford stacks

Being an algebraic stack or a Deligne-Mumford stack over a scheme `S` is
invariant under bicategorical equivalence in `GroupoidsOver S`.
-/

@[expose] public section

open CategoryTheory AlgebraicGeometry
open scoped Bicategory

noncomputable section

universe u

namespace AlgebraicGeometry

namespace AlgebraicStack

/-- Being an algebraic stack is closed under bicategorical equivalence of
categories fibred in groupoids over `(Sch/S)_fppf`. -/
instance objectProperty.isClosedUnderEquivalences (S : Scheme.{u}) :
    (objectProperty S).IsClosedUnderEquivalences := sorry

/-- An algebraic stack remains an algebraic stack after transport across an
equivalence of categories fibred in groupoids over `(Sch/S)_fppf`. -/
theorem of_equivalence {S : Scheme.{u}} {X Y : GroupoidsOver S} (e : X ≌ Y)
    [AlgebraicStack X] : AlgebraicStack Y := sorry

/-- Equivalent categories fibred in groupoids over `(Sch/S)_fppf` are algebraic
stacks simultaneously. -/
theorem iff_of_equivalence {S : Scheme.{u}} {X Y : GroupoidsOver S} (e : X ≌ Y) :
    AlgebraicStack X ↔ AlgebraicStack Y := sorry

end AlgebraicStack

namespace DeligneMumfordStack

/-- Being a Deligne-Mumford stack is closed under bicategorical equivalence of
categories fibred in groupoids over `(Sch/S)_fppf`. -/
instance objectProperty.isClosedUnderEquivalences (S : Scheme.{u}) :
    (objectProperty S).IsClosedUnderEquivalences := sorry

/-- A Deligne-Mumford stack remains a Deligne-Mumford stack after transport
across an equivalence of categories fibred in groupoids over `(Sch/S)_fppf`. -/
theorem of_equivalence {S : Scheme.{u}} {X Y : GroupoidsOver S} (e : X ≌ Y)
    [DeligneMumfordStack X] : DeligneMumfordStack Y := sorry

/-- Equivalent categories fibred in groupoids over `(Sch/S)_fppf` are
Deligne-Mumford stacks simultaneously. -/
theorem iff_of_equivalence {S : Scheme.{u}} {X Y : GroupoidsOver S} (e : X ≌ Y) :
    DeligneMumfordStack X ↔ DeligneMumfordStack Y := sorry

end DeligneMumfordStack

end AlgebraicGeometry
