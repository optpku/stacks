/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import ReasLib.CategoryTheory.Fibered.Pushforward.Map.Fibered
public import ReasLib.CategoryTheory.Fibered.Stack.Stackification
public import ReasLib.CategoryTheory.Fibered.Stack.Stackification.Pushforward.Map
import Mathlib.Tactic.CrossRefAttribute

/-!
# Pushforward and stackification

An explicitly certified localized pushforward map preserves a stackification after
postcomposition with any stackification of its target. The universe-polymorphic owner is stated
for cartesian based functors; the fixed-owner statement is its `FiberedCategoryOver`
specialization. Neither a chosen inverse image nor a morphism-of-sites package is part of the
mathematical statement.

The same import exposes the universe-polymorphic pushforward Hom functor, its pullback
comparison, and transport through an explicitly supplied quasi-inverse. These constructions
remain in the `CartesianBasedFunctor.PushforwardHom` namespace, so downstream developments can
use them without passing through a bundled inverse-image stack.

## Main declarations

* `CartesianBasedFunctor.IsStackification.pushforward_comp` -- compatibility of pushforward
  with heterogeneous stackifications.
* `CartesianBasedFunctor.PushforwardHom.functor` -- the neutral pushforward Hom functor.
* `CartesianBasedFunctor.PushforwardHom.pullbackComparison` -- its canonical pullback
  comparison.
* `CartesianBasedFunctor.PushforwardHom.mapFunctor` -- transport through an explicit
  quasi-inverse, with comparison and choice-coherence API.
-/

@[expose] public section

universe uC uD uS uT uR vC vD vS vT vR w₀ w₁

namespace CategoryTheory

open Limits

variable {C : Type uC} {D : Type uD}
variable [Category.{vC} C] [Category.{vD} D]
variable {J : GrothendieckTopology C} {K : GrothendieckTopology D}

namespace CartesianBasedFunctor.IsStackification

variable {S : Type uS} {T : Type uT} {R : Type uR}
variable [Category.{vS} S] [Category.{vT} T] [Category.{vR} R]
variable {p : S ⥤ C} {q : T ⥤ C} {r : R ⥤ D}

/-- Localized pushforward followed by a stackification of the pushed-forward target carries
every source stackification to a stackification. This is the heterogeneous owner: all three
total categories may live in independent universes. -/
@[stacks 04WR "heterogeneous pushforward composition of stackifications"]
theorem pushforward_comp
    {u : C ⥤ D} [u.IsContinuous J K]
    [p.IsFibered] [q.IsFibered] [r.IsFibered]
    [HasPullbacks C] [HasEqualizers C]
    [PreservesLimitsOfShape WalkingCospan u]
    [PreservesLimitsOfShape WalkingParallelPair u]
    {G : CartesianBasedFunctor p q}
    (hG : CartesianBasedFunctor.IsStackification J G)
    (hp : Functor.Pushforward.ProjectionChoice u p)
    (hq : Functor.Pushforward.ProjectionChoice u q)
    (h_inverts : Functor.Pushforward.sourceMap.inverts u G)
    {H : CartesianBasedFunctor (u.pushforwardProjection q hq) r}
    (hH : CartesianBasedFunctor.IsStackification K H) :
    CartesianBasedFunctor.IsStackification K
      ((CartesianBasedFunctor.Pushforward.map u G hp hq h_inverts).comp H) := sorry

end CartesianBasedFunctor.IsStackification

namespace FiberedCategoryOver.Hom.IsStackification

/-- Localized pushforward followed by a stackification of the pushed-forward
target carries every source stackification to a stackification.  Only
pullbacks and equalizers, and preservation of those shapes, are required. -/
@[stacks 04WR "fixed-universe pushforward composition of stackifications"]
theorem pushforward_comp
    {u : C ⥤ D} [u.IsContinuous J K]
    [HasPullbacks C] [HasEqualizers C]
    [PreservesLimitsOfShape WalkingCospan u]
    [PreservesLimitsOfShape WalkingParallelPair u]
    {X Y : FiberedCategoryOver.{uC, vC,
      max w₀ (max uC (max uD (max vC vD))),
      max w₁ (max w₀ (max uC (max uD (max vC vD))))} C}
    {Z : FiberedCategoryOver.{uD, vD,
      max w₀ (max uC (max uD (max vC vD))),
      max w₁ (max w₀ (max uC (max uD (max vC vD))))} D}
    {G : X ⟶ Y} (hG : FiberedCategoryOver.Hom.IsStackification J G)
    (hX : FiberedCategoryOver.Pushforward.ProjectionChoice u X)
    (hY : FiberedCategoryOver.Pushforward.ProjectionChoice u Y)
    (h_inverts : Functor.Pushforward.sourceMap.inverts u
      (FiberedCategoryOver.toCartesianBasedFunctor G))
    {H : FiberedCategoryOver.pushforward u Y hY ⟶ Z}
    (hH : FiberedCategoryOver.Hom.IsStackification K H) :
    FiberedCategoryOver.Hom.IsStackification K
      (FiberedCategoryOver.Pushforward.map u G hX hY h_inverts ≫ H) := sorry

end FiberedCategoryOver.Hom.IsStackification

end CategoryTheory
