/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import ReasLib.CategoryTheory.Fibered.Pushforward.Map.TwoCell.CartesianBasedFunctor.Construction
import Mathlib.Tactic.CrossRefAttribute

/-!
# Functoriality of cartesian pushforward two-cells

This file owns the identity and composition laws and the Hom functor for cartesian pushforward.
-/

@[expose] public section

universe uC uD uS uT vC vD vS vT

namespace CategoryTheory.CartesianBasedFunctor.Pushforward

open Limits
open scoped Bicategory Functor

variable {C : Type uC} {D : Type uD}
variable {S : Type uS} {T : Type uT}
variable [Category.{vC} C] [Category.{vD} D]
variable [Category.{vS} S] [Category.{vT} T]
variable {p : S ⥤ C} {q : T ⥤ C} [p.IsFibered] [q.IsFibered]
variable (u : C ⥤ D) [HasPullbacks C] [HasEqualizers C]
variable [PreservesLimitsOfShape WalkingCospan u]
variable [PreservesLimitsOfShape WalkingParallelPair u]

/-- Cartesian pushforward preserves identity transformations for a fixed explicit endpoint
proof. -/
@[simp, stacks 04WI "cartesian pushforward two-cell identity"]
theorem map₂.id (F : CartesianBasedFunctor p q)
    (hp : Functor.Pushforward.ProjectionChoice u p)
    (hq : Functor.Pushforward.ProjectionChoice u q)
    (hF : Functor.Pushforward.sourceMap.inverts u F) :
    map₂ u hp hq hF hF (𝟙 F) = 𝟙 (map u F hp hq hF) := sorry

/-- Cartesian pushforward preserves vertical composition for explicit endpoint proofs. -/
@[simp, stacks 04WI "cartesian pushforward two-cell composition"]
theorem map₂.comp {F G H : CartesianBasedFunctor p q}
    (hp : Functor.Pushforward.ProjectionChoice u p)
    (hq : Functor.Pushforward.ProjectionChoice u q)
    (hF : Functor.Pushforward.sourceMap.inverts u F)
    (hG : Functor.Pushforward.sourceMap.inverts u G)
    (hH : Functor.Pushforward.sourceMap.inverts u H)
    (eta : F ⟶ G) (theta : G ⟶ H) :
    map₂ u hp hq hF hH (eta ≫ theta) =
      map₂ u hp hq hF hG eta ≫ map₂ u hp hq hG hH theta := sorry

/-- Pushforward as a functor between categories of cartesian based functors, formed from an
explicit family of inversion proofs. -/
@[stacks 04WI "cartesian pushforward Hom functor"]
noncomputable def mapFunctor
    (h : InversionChoice u p q) :
    CartesianBasedFunctor p q ⥤
      CartesianBasedFunctor (u.pushforwardProjection p h.source)
        (u.pushforwardProjection q h.target) where
  obj F := map.ofInversionChoice u F h
  map {_ _} eta := map₂.ofInversionChoice u h eta
  map_id F := map₂.ofInversionChoice.id u h F
  map_comp eta theta := map₂.ofInversionChoice.comp u h eta theta

/-- The object action of cartesian pushforward uses the supplied inversion proof. -/
@[simp, stacks 04WI "cartesian pushforward Hom functor object"]
theorem mapFunctor.obj (h : InversionChoice u p q)
    (F : CartesianBasedFunctor p q) :
    (mapFunctor u h).obj F =
      map u F h.source h.target (h.inverts F) := sorry

/-- The morphism action of cartesian pushforward uses the supplied endpoint proofs. -/
@[simp, stacks 04WI "cartesian pushforward Hom functor map"]
theorem mapFunctor.map (h : InversionChoice u p q)
    {F G : CartesianBasedFunctor p q} (eta : F ⟶ G) :
    (mapFunctor u h).map eta =
      map₂.ofInversionChoice u h eta := sorry

end CategoryTheory.CartesianBasedFunctor.Pushforward

-- Data audit: `InversionChoice` is Prop-valued evidence; the Hom functor receives it explicitly.
