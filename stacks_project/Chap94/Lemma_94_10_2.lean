module

public import Mathlib.CategoryTheory.MorphismProperty.Local
public import stacks_project.Chap73.Lemma_73_7_3_Precoverage
public import stacks_project.Chap100.Lemma_100_3_2_MorphismProperty

/-!
# Equivalence-invariance of having a morphism property

A property `P` as in Definition 94.10.1 is invariant under 2-commutative
squares of 1-morphisms of groupoid fibrations over `(Sch/S)_fppf` whose
horizontal arrows are equivalences.
-/

@[expose] public section

open CategoryTheory AlgebraicGeometry
open scoped Bicategory

noncomputable section

universe u

namespace AlgebraicGeometry.Groupoids.Hom

/-- Lemma 94.10.2: let `S` be an object of `Sch_fppf`. Let `P` be as in
Definition 94.10.1. Consider a 2-commutative diagram of 1-morphisms of
categories fibred in groupoids over `(Sch/S)_fppf`, with horizontal arrows
equivalences `eX : X' ≌ X` and `eY : Y' ≌ Y` and vertical arrows `f : X ⟶ Y`
and `f' : X' ⟶ Y'`. Assume `f` is representable by algebraic spaces
(equivalently `f'`, by Lemma 94.9.3). Then `has P f` if and only if
`has P f'`. -/
@[stacks 0459]
theorem has.iff_of_equivalence {S : Scheme.{u}} {X' X Y' Y : GroupoidsOver S}
    (P : MorphismProperty (AlgebraicSpace S))
    [P.IsStableUnderBaseChange]
    [P.IsLocalAtTarget (AlgebraicSpace.fppfPrecoverage S)]
    (eX : X' ≌ X) (eY : Y' ≌ Y) (f : X ⟶ Y) (f' : X' ⟶ Y')
    (sq : eX.hom ≫ f ≅ f' ≫ eY.hom)
    (hf : relativelyRepresentableByAlgebraicSpaces f) :
    has P f ↔ has P f' := sorry

end AlgebraicGeometry.Groupoids.Hom
