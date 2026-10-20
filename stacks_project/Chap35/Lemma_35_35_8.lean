/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

import ReasLib.AlgebraicGeometry.Scheme.DescentData.Pullback.FullyFaithful
import StacksCheckRecall

open CategoryTheory

universe u

namespace AlgebraicGeometry
namespace Scheme
namespace DescentData
namespace Pullback

/- Lemma 35.35.8: if `f : X ⟶ X'` is a morphism over `S` and the singleton family
`{X ⟶ S}` is an fpqc covering, then pullback along `f` from descent data relative to
`X'/S` to descent data relative to `X/S` is fully faithful. -/
@[stacks 040K] #check
  (AlgebraicGeometry.Scheme.DescentData.Pullback.fullyFaithfulOfFpqcDomain :
    {X X' S : Scheme.{u}} → (a : X ⟶ S) → (a' : X' ⟶ S) →
      (f : X ⟶ X') → (sq : CommSq f a a' (𝟙 S)) →
        Scheme.FpqcCovering (fun _ : Unit ↦ Over.mk a) →
          Nonempty (functor a' a (𝟙 S) f sq).FullyFaithful)

end Pullback
end DescentData
end Scheme
end AlgebraicGeometry
