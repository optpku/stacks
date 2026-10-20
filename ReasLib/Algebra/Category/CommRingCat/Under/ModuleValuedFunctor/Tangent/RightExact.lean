/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.Algebra.Category.CommRingCat.Under.ModuleValuedFunctor.Exact
public import ReasLib.Algebra.Category.CommRingCat.Under.ModuleValuedFunctor.Pullback
public import ReasLib.Algebra.Category.CommRingCat.Under.ModuleValuedFunctor.Tangent
public import ReasLib.CategoryTheory.Functor.Exactness.ShortExact

@[expose] public section

open CategoryTheory

universe u

namespace ModuleValuedFunctor

variable {A : CommRingCat.{u}}

/-- A module-valued functor is tangent-right-exact when each of its fixed-base tangent
functors on modules is right exact. -/
def TangentRightExact (F : ModuleValuedFunctor.{u, u} A) : Prop :=
  ∀ B, rightExactFunctor (ModuleCat.{u} B.right) (ModuleCat.{u} B.right)
    (F.tangent.fixedBase B)

namespace TangentRightExact

/-- In a pointwise short exact pair, tangent right exactness of the first two terms
implies tangent right exactness of the third. -/
theorem of_pointwiseShortExact_left_middle
    {F G H : ModuleValuedFunctor.{u, u} A} (f : Hom F G) (g : Hom G H)
    (hfg : f.IsPointwiseShortExact g) (hF : TangentRightExact F)
    (hG : TangentRightExact G) : TangentRightExact H := sorry

/-- In a pointwise short exact pair, tangent right exactness of the outer terms
implies tangent right exactness of the middle term. -/
theorem of_pointwiseShortExact_ends
    {F G H : ModuleValuedFunctor.{u, u} A} (f : Hom F G) (g : Hom G H)
    (hfg : f.IsPointwiseShortExact g) (hF : TangentRightExact F)
    (hH : TangentRightExact H) : TangentRightExact G := sorry

/-- Tangent right exactness is preserved by pulling back the second map in a pointwise
short exact pair along a morphism from another tangent-right-exact functor. -/
theorem pullback_of_pointwiseShortExact
    {F G H H' : ModuleValuedFunctor.{u, u} A} (f : Hom F G) (g : Hom G H)
    (hfg : f.IsPointwiseShortExact g) (α : Hom H' H)
    (hF : TangentRightExact F) (hG : TangentRightExact G)
    (hH : TangentRightExact H) (hH' : TangentRightExact H') :
    TangentRightExact (pullback g α) := sorry

end TangentRightExact

end ModuleValuedFunctor
