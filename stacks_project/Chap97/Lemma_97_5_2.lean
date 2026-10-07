module

public import stacks_project.Chap97.«97_5_0_1_OnObjects»

/-!
# Composition of morphisms limit preserving on objects

The composition of 1-morphisms of categories fibred in groupoids that are
limit preserving on objects is again limit preserving on objects.
-/

@[expose] public section

open CategoryTheory AlgebraicGeometry
open scoped Bicategory

noncomputable section

universe u

namespace AlgebraicGeometry.Groupoids.Hom

namespace LimitPreservingOnObjects

/-- Lemma 97.5.2: If `p : X ⟶ Y` and `q : Y ⟶ Z` are 1-morphisms of categories
fibred in groupoids over `(Sch/S)_fppf` and both are limit preserving on objects,
then so is the composition `q ∘ p`, written `p ≫ q`. -/
@[stacks 06CW]
instance comp {S : Scheme.{u}} {X Y Z : GroupoidsOver S}
    (p : X ⟶ Y) (q : Y ⟶ Z) [LimitPreservingOnObjects p] [LimitPreservingOnObjects q] :
    LimitPreservingOnObjects (p ≫ q) := sorry

end LimitPreservingOnObjects

end AlgebraicGeometry.Groupoids.Hom
