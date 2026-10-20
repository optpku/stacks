/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.AlgebraicGeometry.GroupoidsOver.SurjectiveOnObjects
import StacksCheckRecall

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

/- Lemma 97.7.2: If `p : X ⟶ Y` and `q : Y ⟶ Z` are 1-morphisms of categories
fibred in groupoids over `(Sch/S)_fppf` and both are surjective on objects, then
so is the composition `q ∘ p`, written `p ≫ q`. -/
@[stacks 06D6] #check (AlgebraicGeometry.Groupoids.Hom.SurjectiveOnObjects.comp :
  ∀ {S : Scheme.{u}} {X Y Z : GroupoidsOver S}
    (f : X ⟶ Y) (g : Y ⟶ Z) [SurjectiveOnObjects f] [SurjectiveOnObjects g],
    SurjectiveOnObjects (f ≫ g))

end SurjectiveOnObjects

end AlgebraicGeometry.Groupoids.Hom
