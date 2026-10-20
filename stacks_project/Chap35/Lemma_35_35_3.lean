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

/- Lemma 35.35.3: if the top morphism in a commutative square of schemes is flat and
surjective, then the induced pullback functor on singleton-family descent data is faithful. -/
@[stacks 0240] #check
  (AlgebraicGeometry.Scheme.DescentData.Pullback.instFaithfulFunctorOfFlatSurjective :
    ∀ {X X' S S' : Scheme.{u}} (a : X ⟶ S) (a' : X' ⟶ S')
      (h : S' ⟶ S) (f : X' ⟶ X) (sq : CommSq f a' a h) [Flat f] [Surjective f],
      (functor a a' h f sq).Faithful)

end Pullback
end DescentData
end Scheme
end AlgebraicGeometry
