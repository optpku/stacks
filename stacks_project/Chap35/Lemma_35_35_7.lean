/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.AlgebraicGeometry.Scheme.DescentData.Pullback.Faithful
import StacksCheckRecall

open CategoryTheory

universe u

namespace AlgebraicGeometry
namespace Scheme
namespace DescentData
namespace Pullback

/- Lemma 35.35.7: if `f : X ⟶ X'` is a morphism over `S` and `X ⟶ S` is flat and
surjective, then pullback along `f` from descent data relative to `X'/S` to descent data
relative to `X/S` is faithful. -/
@[stacks 040J] #check
  (AlgebraicGeometry.Scheme.DescentData.Pullback.instFaithfulFunctorOfFlatSurjectiveDomain :
    ∀ {X X' S : Scheme.{u}} (a : X ⟶ S) (a' : X' ⟶ S)
      (f : X ⟶ X') (sq : CommSq f a a' (𝟙 S)) [Flat a] [Surjective a],
      (functor a' a (𝟙 S) f sq).Faithful)

end Pullback
end DescentData
end Scheme
end AlgebraicGeometry
