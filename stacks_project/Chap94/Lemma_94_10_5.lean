module

public import ReasLib.AlgebraicGeometry.GroupoidsOver.Representable.Property.Composition
import StacksCheckRecall

@[expose] public section

open CategoryTheory AlgebraicGeometry
open Groupoids.Hom
open scoped Bicategory

universe u

/- Lemma 94.10.5: let `S` be a scheme in `Sch_fppf`. Let `X`, `Y`, `Z` be
categories fibred in groupoids over `(Sch/S)_fppf`. Let `P` be a property of
morphisms of algebraic spaces as in Definition 94.10.1 that is stable under
composition. Let `f : X ⟶ Y` and `g : Y ⟶ Z` be 1-morphisms representable by
algebraic spaces. If `f` and `g` have `P`, then so does `f ≫ g` (Stacks `g ∘ f`).
Representability of the composite is Lemma 94.9.9, not this conclusion. -/
@[stacks 045B]
#check (AlgebraicGeometry.Groupoids.Hom.has.comp :
    ∀ {S : Scheme.{u}} {X Y Z : GroupoidsOver S}
    (P : MorphismProperty (AlgebraicSpace S))
    [P.IsStableUnderBaseChange]
    [P.IsLocalAtTarget (AlgebraicSpace.fppfPrecoverage S)]
    [P.IsStableUnderComposition]
    (f : X ⟶ Y) (g : Y ⟶ Z)
    (hf : relativelyRepresentableByAlgebraicSpaces f)
    (hg : relativelyRepresentableByAlgebraicSpaces g)
    (hfP : has P f) (hgP : has P g), has P (f ≫ g))
