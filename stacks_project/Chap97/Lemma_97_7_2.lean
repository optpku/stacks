module

public import stacks_project.Chap97.Lemma_97_7_1_SurjectiveOnObjects

/-!
# Composition of morphisms surjective on objects

The composition of 1-morphisms of categories fibred in groupoids that are
surjective on objects is again surjective on objects.
-/

@[expose] public section

open CategoryTheory AlgebraicGeometry
open scoped Bicategory

noncomputable section

universe u

namespace AlgebraicGeometry.Groupoids.Hom

namespace SurjectiveOnObjects

/-- Lemma 97.7.2: If `p : X ⟶ Y` and `q : Y ⟶ Z` are 1-morphisms of categories
fibred in groupoids over `(Sch/S)_fppf` and both are surjective on objects, then
so is the composition `q ∘ p`, written `p ≫ q`. -/
@[stacks 06D6]
instance comp {S : Scheme.{u}} {X Y Z : GroupoidsOver S}
    (f : X ⟶ Y) (g : Y ⟶ Z) [SurjectiveOnObjects f] [SurjectiveOnObjects g] :
    SurjectiveOnObjects (f ≫ g) := sorry

end SurjectiveOnObjects

end AlgebraicGeometry.Groupoids.Hom
