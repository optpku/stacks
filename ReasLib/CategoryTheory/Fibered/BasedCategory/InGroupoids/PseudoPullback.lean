/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import ReasLib.CategoryTheory.Fibered.BasedCategory.InGroupoids
public import ReasLib.CategoryTheory.Fibered.InGroupoids.PseudoPullback
public import ReasLib.CategoryTheory.Fibered.PseudoPullback.Closure

/-!
# Pseudo-pullback closure of groupoid-fibred based categories

Object-property closure of `BasedCategory.isFiberedInGroupoids` under the explicit chosen based
pseudo-pullback. The raw projection instances are owned by
`BasedCategory.PseudoPullback.Projection.inGroupoids`; this leaf turns them into reusable
object-property facts.
-/

@[expose] public section

universe u v w vB uX vX uY vY uS vS

namespace CategoryTheory

open ObjectProperty
open scoped BasedFunctor

variable {C : Type u} [Category.{v} C]

namespace BasedCategory

namespace isFiberedInGroupoids

/-- The chosen pseudo-pullback of cartesian morphisms whose sources are fibred in groupoids is
again fibred in groupoids. This is the universe-polymorphic object-property form of
`PseudoPullback.Projection.InGroupoids.ofCartesian`; the common target need not satisfy the
property. -/
theorem PseudoPullback.ofCartesian
    {X : BasedCategory.{vX, uX} C}
    {Y : BasedCategory.{vY, uY} C}
    {S : BasedCategory.{vS, uS} C}
    (hX : isFiberedInGroupoids C X)
    (hY : isFiberedInGroupoids C Y)
    (F : CartesianBasedFunctor X.p S.p) (G : CartesianBasedFunctor Y.p S.p) :
    isFiberedInGroupoids C
      (PseudoPullback F.toBasedFunctor G.toBasedFunctor) := sorry
/- Proof strategy: install `hX` and `hY` as the corresponding projection instances, then apply
`PseudoPullback.Projection.InGroupoids.ofCartesian F G`. -/

/-- The chosen pseudo-pullback of a cospan of categories fibred in groupoids is again fibred in
groupoids. All three total categories may live in independent universes; this theorem is the
general semantic closure API, while `PseudoPullback.isClosedUnder` below is its stable-universe
typeclass specialization. -/
theorem pseudoPullback
    {X : BasedCategory.{vX, uX} C}
    {Y : BasedCategory.{vY, uY} C}
    {S : BasedCategory.{vS, uS} C}
    (hX : isFiberedInGroupoids C X)
    (hY : isFiberedInGroupoids C Y)
    (hS : isFiberedInGroupoids C S)
    (F : X ⥤ᵇ S) (G : Y ⥤ᵇ S) :
    isFiberedInGroupoids C (PseudoPullback F G) := sorry
/- Proof strategy: install `hX`, `hY`, and `hS` as the corresponding projection instances, then
apply `PseudoPullback.Projection.inGroupoids F G`. -/

/-- The universe-stable owner used by the generic property-selected two-fibre-product facade is
closed under the chosen based pseudo-pullback. The additional hom universe `vB` is independent of
the base-category hom universe `v`; for completely unrelated total-category universes, use
`pseudoPullback` directly. -/
instance PseudoPullback.isClosedUnder :
    BasedCategory.PseudoPullback.ObjectProperty.IsClosedUnder
      (isFiberedInGroupoids C :
        ObjectProperty
          (BasedCategory.{max v vB, max w (max u (max v vB))} C)) := sorry
/- Proof strategy: specialize `pseudoPullback` to the stable universe
chosen by `BasedCategory.PseudoPullback.ObjectProperty.IsClosedUnder`. -/

end isFiberedInGroupoids

end BasedCategory

end CategoryTheory
