/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import ReasLib.CategoryTheory.Fibered.DiscreteFibration.PresheafEquivalence.Equivalence.Fibration

/-!
# Equivalence instances for the discrete Grothendieck correspondence

This leaf installs the equivalence facts after both explicit comparison isomorphisms have been
constructed.
-/

@[expose] public section

universe w u v

namespace CategoryTheory

variable {C : Type u} [Category.{v} C]

namespace FiberedCategoryOver.Sets

/-- The discrete Grothendieck construction is an equivalence from set-valued presheaves on `C`
to categories fibred in sets over `C`. Its canonical quasi-inverse is `toPresheaf`. -/
@[stacks 02Y2 "discrete Grothendieck construction is an equivalence"]
instance ofPresheaf.isEquivalence :
    (ofPresheaf C :
      (Cᵒᵖ ⥤ Type (max w u)) ⥤ FiberedCategoryOver.Sets C).IsEquivalence := sorry

/-- Straightening is an equivalence on the size-stable category of categories fibred in sets.
Its canonical quasi-inverse is the discrete Grothendieck construction. -/
instance toPresheaf.isEquivalence :
    (toPresheaf C :
      FiberedCategoryOver.Sets.{u, v, max w u, v} C ⥤
        (Cᵒᵖ ⥤ Type (max w u))).IsEquivalence := sorry

end FiberedCategoryOver.Sets

end CategoryTheory
