module

public import ReasLib.CategoryTheory.Fibered.BasedCategory.Equivalence.Bicategorical
public import ReasLib.CategoryTheory.Fibered.BasedCategory.Equivalence.Fiber

/-!
# Fiber functors induced by equivalences over a base

This module records the canonical equivalence property of the functor induced on each standard
fiber by an equivalence in `BasedCategory`.
-/

@[expose] public section

universe v u vS uS

namespace CategoryTheory

open scoped Bicategory

variable {C : Type u} [Category.{v} C]

namespace BasedCategory.Equivalence

variable {X Y : BasedCategory.{vS, uS} C}

/-- The forward `1`-morphism of an equivalence in `BasedCategory C` induces an equivalence on every
standard fiber. -/
theorem fiberFunctor.isEquivalence (e : X ≌ Y) (U : C) :
    (e.hom.fiberFunctor U).IsEquivalence := sorry
/- Proof strategy: use `BasedFunctor.fiberFunctor.isEquivalence e.hom U`; the canonical
`BasedFunctor.homIsEquivalence e` instance supplies equivalence-over-the-base data for `e.hom`. -/

end BasedCategory.Equivalence

end CategoryTheory
