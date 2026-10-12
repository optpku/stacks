/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import Mathlib.CategoryTheory.Equivalence
public import ReasLib.CategoryTheory.Fibered.BasedCategory.Equivalence.Basic
public import ReasLib.CategoryTheory.Fibered.BasedCategory.Postcomposition

/-!
# Equivalences induced by postcomposition over a base

This module transports an explicit equivalence-over-base, or its
`BasedFunctor.IsEquivalence` property, through heterogeneous postcomposition on
based-functor hom-categories.
-/

@[expose] public section

universe v u vX uX vY uY vZ uZ

namespace CategoryTheory

open scoped BasedFunctor

variable {C : Type u} [Category.{v} C]

namespace BasedCategory

/-- Postcomposition by a based functor with explicit quasi-inverse data is an equivalence of
heterogeneous based-functor hom-categories. Its quasi-inverse is postcomposition by
`e.inverse`. -/
theorem postcomposition.isEquivalence_of_quasiInverse
    (X : BasedCategory.{vX, uX} C) {Y : BasedCategory.{vY, uY} C}
    {Z : BasedCategory.{vZ, uZ} C} {G : Y ⥤ᵇ Z}
    (e : BasedFunctor.QuasiInverse G) :
    (postcomposition X G).IsEquivalence := sorry
/- Proof strategy: use `postcomposition X e.inverse` as a quasi-inverse. The two required
natural isomorphisms are induced by the unit and counit of `e`, together with
`postcomposition.comp` and `postcomposition.id`. -/

/-- Postcomposition by an equivalence over the base is an equivalence of heterogeneous
based-functor hom-categories. -/
@[instance]
theorem postcomposition.isEquivalence
    (X : BasedCategory.{vX, uX} C) {Y : BasedCategory.{vY, uY} C}
    {Z : BasedCategory.{vZ, uZ} C} (G : Y ⥤ᵇ Z)
    [BasedFunctor.IsEquivalence G] :
    (postcomposition X G).IsEquivalence := sorry
/- Proof strategy: apply `postcomposition.isEquivalence_of_quasiInverse` to the named
choice boundary `G.asQuasiInverse`. The theorem exposes only the resulting proposition, not
the selected quasi-inverse data. -/

end BasedCategory

end CategoryTheory
