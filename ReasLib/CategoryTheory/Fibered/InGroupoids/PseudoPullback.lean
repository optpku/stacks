/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.CategoryTheory.Fibered.InGroupoids
public import ReasLib.CategoryTheory.Fibered.InGroupoids.Cartesian
public import ReasLib.CategoryTheory.Fibered.PseudoPullback.Closure
public import ReasLib.CategoryTheory.Fibered.PseudoPullback.Fiber
public import ReasLib.CategoryTheory.Limits.CategoricalPullback.Groupoid
import Mathlib.Tactic.CrossRefAttribute

/-!
# Based pseudo-pullbacks of groupoid fibrations

Closure of `Functor.IsFibered.InGroupoids` under the explicit based pseudo-pullback model and
its two projections. The statements concern raw projections and based functors, without choosing
the full subbicategory of groupoid-fibred categories.
-/

@[expose] public section

universe u v uX vX uY vY uS vS

namespace CategoryTheory

open BasedCategory Bicategory ObjectProperty
open scoped Bicategory BasedFunctor

variable {C : Type u} [Category.{v} C]

namespace BasedCategory.PseudoPullback

variable {X : BasedCategory.{vX, uX} C}
variable {Y : BasedCategory.{vY, uY} C}
variable {S : BasedCategory.{vS, uS} C}

/-- The first projection from a pseudo-pullback of cartesian functors is fibred when its base
source is fibred in groupoids and the opposite source is fibred. No groupoid condition is needed
on the fibers of the opposite source or the common target. -/
instance Fst.IsFibered.ofCartesian
    (F : CartesianBasedFunctor X.p S.p) (G : CartesianBasedFunctor Y.p S.p)
    [Functor.IsFibered.InGroupoids X.p] [Y.p.IsFibered] :
    (PseudoPullback.fst F.toBasedFunctor G.toBasedFunctor).toFunctor.IsFibered := sorry

/-- The second projection from a pseudo-pullback of cartesian functors is fibred when its base
source is fibred in groupoids and the opposite source is fibred. This is the symmetric companion
to `Fst.IsFibered.ofCartesian`. -/
instance Snd.IsFibered.ofCartesian
    (F : CartesianBasedFunctor X.p S.p) (G : CartesianBasedFunctor Y.p S.p)
    [X.p.IsFibered] [Functor.IsFibered.InGroupoids Y.p] :
    (PseudoPullback.snd F.toBasedFunctor G.toBasedFunctor).toFunctor.IsFibered := sorry

/-- Every standard fibre of the explicit based pseudo-pullback projection is a groupoid. -/
instance Fiber.isGroupoid (F : X ⥤ᵇ S) (G : Y ⥤ᵇ S) (U : C)
    [IsGroupoid (X.p.Fiber U)] [IsGroupoid (Y.p.Fiber U)] :
    IsGroupoid ((BasedCategory.PseudoPullback F G).p.Fiber U) := sorry
/- Proof strategy: transport across the fibre equivalence with a categorical pullback of the two
source fibres, which is a groupoid by `Limits.CategoricalPullback.isGroupoid`. -/

/-- The pseudo-pullback of two cartesian based functors with groupoid-fibred domains is again
fibred in groupoids. The common target need not itself be fibred in groupoids: its only role in
the fibredness argument is through preservation of strongly cartesian arrows by the two legs. -/
instance Projection.InGroupoids.ofCartesian
    (F : CartesianBasedFunctor X.p S.p) (G : CartesianBasedFunctor Y.p S.p)
    [Functor.IsFibered.InGroupoids X.p]
    [Functor.IsFibered.InGroupoids Y.p] :
    Functor.IsFibered.InGroupoids
      (BasedCategory.PseudoPullback F.toBasedFunctor G.toBasedFunctor).p := sorry
/- Proof strategy: use `BasedCategory.PseudoPullback.projectionIsFibered F G` for fibredness and
`Fiber.isGroupoid F.toBasedFunctor G.toBasedFunctor` on each standard fibre. -/

/-- The projection of a based pseudo-pullback of categories fibred
in groupoids is again fibred in groupoids. This is the convenient unbundled specialization of
`Projection.InGroupoids.ofCartesian`: every based functor into the groupoid-fibred common target
preserves strongly cartesian arrows. -/
@[stacks 0041 "(1)"]
instance Projection.inGroupoids (F : X ⥤ᵇ S) (G : Y ⥤ᵇ S)
    [Functor.IsFibered.InGroupoids X.p] [Functor.IsFibered.InGroupoids Y.p]
    [Functor.IsFibered.InGroupoids S.p] :
    Functor.IsFibered.InGroupoids (BasedCategory.PseudoPullback F G).p := sorry
/- Proof strategy: bundle `F` and `G` as cartesian based functors using
`BasedFunctor.PreservesStronglyCartesian.ofTargetInGroupoids`, then apply
`Projection.InGroupoids.ofCartesian`. -/

/-- The first projection from the pseudo-pullback of cartesian morphisms between
groupoid-fibred sources is fibred in groupoids. The common target need not itself be fibred in
groupoids. -/
instance Fst.InGroupoids.ofCartesian
    (F : CartesianBasedFunctor X.p S.p) (G : CartesianBasedFunctor Y.p S.p)
    [Functor.IsFibered.InGroupoids X.p]
    [Functor.IsFibered.InGroupoids Y.p] :
    Functor.IsFibered.InGroupoids
      (PseudoPullback.fst F.toBasedFunctor G.toBasedFunctor).toFunctor := sorry
/- Proof strategy: lift an arrow through `Y.p`. Both its image under `G` and the image under `F`
of the given arrow of `X` are strongly cartesian, so uniqueness supplies the vertical comparison
isomorphism. The groupoid fibres of `Y.p` identify the fibres of `fst` as groupoids. -/

/-- The second projection from the pseudo-pullback of cartesian morphisms between
groupoid-fibred sources is fibred in groupoids. The common target need not itself be fibred in
groupoids. -/
instance Snd.InGroupoids.ofCartesian
    (F : CartesianBasedFunctor X.p S.p) (G : CartesianBasedFunctor Y.p S.p)
    [Functor.IsFibered.InGroupoids X.p]
    [Functor.IsFibered.InGroupoids Y.p] :
    Functor.IsFibered.InGroupoids
      (PseudoPullback.snd F.toBasedFunctor G.toBasedFunctor).toFunctor := sorry
/- Proof strategy: use the symmetric construction, lifting through `X.p`; the groupoid fibres of
`X.p` give the fibres of `snd`. -/

/-- The first projection from a based pseudo-pullback is fibred in groupoids whenever the
opposite source and the common target are fibred in groupoids. No condition on the projected
source is needed. This is the general base-change API behind the slice specialization in
`PseudoPullback.fstGroupoids`. -/
instance Fst.inGroupoids
    (F : X ⥤ᵇ S) (G : Y ⥤ᵇ S)
    [Functor.IsFibered.InGroupoids Y.p]
    [Functor.IsFibered.InGroupoids S.p] :
    Functor.IsFibered.InGroupoids (PseudoPullback.fst F G).toFunctor := sorry
/- Proof strategy: lift an arrow of `X` through `Y.p`. Every arrow of `S` is strongly cartesian,
so strong-cartesian uniqueness supplies the vertical comparison isomorphism needed for an object
and arrow of the pseudo-pullback. The groupoid fibres of `Y.p` give groupoid fibres of `fst`. -/

/-- The second projection from a based pseudo-pullback is fibred in groupoids whenever the
opposite source and the common target are fibred in groupoids. No condition on the projected
source is needed. -/
instance Snd.inGroupoids
    (F : X ⥤ᵇ S) (G : Y ⥤ᵇ S)
    [Functor.IsFibered.InGroupoids X.p]
    [Functor.IsFibered.InGroupoids S.p] :
    Functor.IsFibered.InGroupoids (PseudoPullback.snd F G).toFunctor := sorry
/- Proof strategy: symmetrically lift an arrow of `Y` through `X.p`, use strong-cartesian
uniqueness in `S` to transport the comparison isomorphism, and use the groupoid fibres of `X.p`
for the fibres of `snd`. -/

end BasedCategory.PseudoPullback

end CategoryTheory
