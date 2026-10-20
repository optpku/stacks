/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

import Mathlib.Tactic.CrossRefAttribute
public import ReasLib.CategoryTheory.Fibered.CartesianBasedFunctor.Basic
public import ReasLib.CategoryTheory.Fibered.InSets.Bicategory
public import ReasLib.CategoryTheory.Fibered.PseudoPullback.Cartesian
public import ReasLib.CategoryTheory.Fibered.PseudoPullback.Closure

/-!
# Pseudo-pullbacks of categories fibred in sets

The explicit based pseudo-pullback of discrete fibrations is again a discrete fibration. The raw
closure statements allow independent universes and separate the stronger cartesian-leg theorem
from its convenient full-property specialization. The final instance supplies the universe-stable
owner used by the common property-selected two-fibre-product API.
-/

@[expose] public section

universe u v w vB uX vX uY vY uS vS

namespace CategoryTheory

open ObjectProperty

variable {C : Type u} [Category.{v} C]

namespace BasedCategory.PseudoPullback

variable {X : BasedCategory.{vX, uX} C}
variable {Y : BasedCategory.{vY, uY} C}
variable {S : BasedCategory.{vS, uS} C}

/-- The pseudo-pullback of cartesian based functors with discrete-fibration domains is again a
discrete fibration. The common target need not be fibred in sets: cartesianity of the two legs
supplies the lifts, while discreteness of the source fibres supplies uniqueness. -/
instance Projection.InSets.ofCartesian
    [Functor.IsDiscreteFibration X.p]
    [Functor.IsDiscreteFibration Y.p]
    (F : CartesianBasedFunctor X.p S.p)
    (G : CartesianBasedFunctor Y.p S.p) :
    Functor.IsDiscreteFibration
      (BasedCategory.PseudoPullback
        F.toBasedFunctor G.toBasedFunctor).p := sorry
/- Proof strategy: use `BasedCategory.PseudoPullback.projectionIsFibered F G` for existence of
cartesian lifts. Every vertical morphism in a fibre of the pseudo-pullback is determined by its
two projected components; discreteness of the source fibres makes both components identities,
and `PseudoPullback.hom_ext` gives uniqueness. -/

/-- Lemma 4.38.4 (1) (Stacks 0047): the explicit pseudo-pullback projection is a discrete
fibration when all three cospan projections are discrete fibrations. This is the convenient
unbundled specialization of `Projection.InSets.ofCartesian`. -/
@[stacks 0047 "(1)"]
instance Projection.inSets
    [Functor.IsDiscreteFibration X.p]
    [Functor.IsDiscreteFibration Y.p]
    [Functor.IsDiscreteFibration S.p]
    (F : X ⥤ᵇ S) (G : Y ⥤ᵇ S) :
    Functor.IsDiscreteFibration
      (BasedCategory.PseudoPullback F G).p := sorry
/- Proof strategy: construct lifts componentwise using discreteness of `X.p` and `Y.p`; uniqueness
in `S` identifies their images, and `PseudoPullback.hom_ext` proves uniqueness of the resulting
lift. -/

end BasedCategory.PseudoPullback

namespace BasedCategory

namespace isFiberedInSets

/-- The chosen pseudo-pullback of cartesian morphisms whose sources are fibred in sets is again
fibred in sets. This is the universe-polymorphic object-property form of
`PseudoPullback.Projection.InSets.ofCartesian`; the common target need not satisfy the property. -/
theorem PseudoPullback.ofCartesian
    {X : BasedCategory.{vX, uX} C}
    {Y : BasedCategory.{vY, uY} C}
    {S : BasedCategory.{vS, uS} C}
    (hX : isFiberedInSets C X)
    (hY : isFiberedInSets C Y)
    (F : CartesianBasedFunctor X.p S.p)
    (G : CartesianBasedFunctor Y.p S.p) :
    isFiberedInSets C
      (PseudoPullback F.toBasedFunctor G.toBasedFunctor) := sorry
/- Proof strategy: install `hX` and `hY` as discrete-fibration instances and apply
`PseudoPullback.Projection.InSets.ofCartesian F G`. -/

/-- The chosen pseudo-pullback of a cospan of categories fibred in sets is again fibred in sets.
All three total categories may live in independent universes; this is the general semantic
closure API. -/
theorem pseudoPullback
    {X : BasedCategory.{vX, uX} C}
    {Y : BasedCategory.{vY, uY} C}
    {S : BasedCategory.{vS, uS} C}
    (hX : isFiberedInSets C X)
    (hY : isFiberedInSets C Y)
    (hS : isFiberedInSets C S)
    (F : X ⥤ᵇ S) (G : Y ⥤ᵇ S) :
    isFiberedInSets C (PseudoPullback F G) := sorry
/- Proof strategy: install `hX`, `hY`, and `hS`; every based functor into a discrete fibration
preserves strongly cartesian arrows, so bundle `F` and `G` as cartesian based functors and apply
`PseudoPullback.ofCartesian`. -/

/-- The universe-stable object property of being fibred in sets is closed under the explicit
based pseudo-pullback. The additional hom universe `vB` is independent of the base-category hom
universe `v`; for unrelated total-category universes, use `pseudoPullback`
directly. -/
instance PseudoPullback.isClosedUnder :
    BasedCategory.PseudoPullback.ObjectProperty.IsClosedUnder
      (isFiberedInSets C :
        ObjectProperty
          (BasedCategory.{max v vB, max w (max u (max v vB))} C)) := sorry
/- Proof strategy: specialize `pseudoPullback` to the stable universe chosen by
`BasedCategory.PseudoPullback.ObjectProperty.IsClosedUnder`. -/

end isFiberedInSets

end BasedCategory

end CategoryTheory
