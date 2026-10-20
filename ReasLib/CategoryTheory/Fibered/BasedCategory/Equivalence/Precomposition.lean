module

public import Mathlib.CategoryTheory.Equivalence
public import ReasLib.CategoryTheory.Fibered.BasedCategory.Equivalence.Basic
public import ReasLib.CategoryTheory.Fibered.BasedCategory.Precomposition

/-!
# Equivalences induced by precomposition over a base

This module transports an explicit equivalence-over-base, or its
`BasedFunctor.IsEquivalence` property, through heterogeneous precomposition on
based-functor hom-categories.
-/

@[expose] public section

universe v u vX uX vY uY vZ uZ

namespace CategoryTheory

open scoped BasedFunctor

variable {C : Type u} [Category.{v} C]

namespace BasedCategory

/-- Precomposition by a based functor with explicit quasi-inverse data is an equivalence of
heterogeneous based-functor hom-categories. Its quasi-inverse is precomposition by
`e.inverse`. -/
theorem precomposition.isEquivalence_of_quasiInverse
    (Z : BasedCategory.{vZ, uZ} C) {X : BasedCategory.{vX, uX} C}
    {Y : BasedCategory.{vY, uY} C} {F : X ⥤ᵇ Y}
    (e : BasedFunctor.QuasiInverse F) :
    (precomposition Z F).IsEquivalence := sorry
/- Proof strategy: use `precomposition Z e.inverse` as a quasi-inverse. The two required
natural isomorphisms are induced by the unit and counit of `e`, together with
`precomposition.comp` and `precomposition.id`. -/

/-- Precomposition by an equivalence over the base is an equivalence of heterogeneous
based-functor hom-categories. -/
@[instance]
theorem precomposition.isEquivalence
    (Z : BasedCategory.{vZ, uZ} C) {X : BasedCategory.{vX, uX} C}
    {Y : BasedCategory.{vY, uY} C} (F : X ⥤ᵇ Y)
    [BasedFunctor.IsEquivalence F] :
    (precomposition Z F).IsEquivalence := sorry
/- Proof strategy: apply `precomposition.isEquivalence_of_quasiInverse` to the named
choice boundary `F.asQuasiInverse`. The theorem exposes only the resulting proposition, not
the selected quasi-inverse data. -/

end BasedCategory

end CategoryTheory
