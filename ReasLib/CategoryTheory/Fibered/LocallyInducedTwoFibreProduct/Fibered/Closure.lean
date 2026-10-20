/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.CategoryTheory.Fibered.LocallyInducedTwoFibreProduct.Basic
public import ReasLib.CategoryTheory.Fibered.PseudoPullback.Fibered

/-!
# Fibred-category closure data for locally induced two-fibre products

This specialization supplies the hom-property instances that make the generic locally induced
construction available for fibred categories and cartesian functors.
-/

@[expose] public section

universe u v w vB

namespace CategoryTheory

open BasedCategory ObjectProperty
open scoped Bicategory BasedFunctor

variable {C : Type u} [Category.{v} C]

namespace FiberedCategoryOver

/-- The cartesian-functor hom property is relatively closed under explicit pseudo-pullbacks:
the pseudo-pullback of two fibred categories along selected cartesian morphisms is fibred. This
is intentionally not a
`BasedCategory.PseudoPullback.ObjectProperty.IsClosedUnder` instance, since arbitrary based
functors between fibred categories need not preserve cartesian arrows. -/
instance homProperty.PseudoPullback.isClosedUnder :
    BasedCategory.PseudoPullback.HomProperty.IsClosedUnder
      (P := BasedCategory.isFibered.{u, v, max w (max u (max v vB)), max v vB} C)
      (homProperty.{u, v, max w (max u (max v vB)), max v vB} C) := sorry
/- Proof strategy: bundle the two selected legs with their stored
`BasedFunctor.PreservesStronglyCartesian` witnesses and apply the canonical
`FiberedCategoryOver.pseudoPullbackIsFibered` bridge. -/

/-- The cartesian-functor hom property contains the two projections of every explicit
pseudo-pullback of selected cospan legs. -/
instance homProperty.projections :
    LocallyInduced.TwoFibreProduct.Projections.Has
      (P := BasedCategory.isFibered.{u, v, max w (max u (max v vB)), max v vB} C)
      (Q := homProperty.{u, v, max w (max u (max v vB)), max v vB} C) := sorry
/- Proof strategy: unfold the class fields and use
`BasedCategory.PseudoPullback.fstPreservesStronglyCartesian` and
`BasedCategory.PseudoPullback.sndPreservesStronglyCartesian`. -/

/-- Preservation of strongly cartesian arrows for a map into an explicit pseudo-pullback is
detected by its two projection composites. -/
instance homProperty.isDetected :
    LocallyInduced.TwoFibreProduct.Projections.IsDetected
      (P := BasedCategory.isFibered.{u, v, max w (max u (max v vB)), max v vB} C)
      (Q := homProperty.{u, v, max w (max u (max v vB)), max v vB} C) := sorry
/- Proof strategy: the class field is the reverse implication of
`BasedCategory.PseudoPullback.preservesStronglyCartesian_iff`. -/

end FiberedCategoryOver

end CategoryTheory
