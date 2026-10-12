/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

import ReasLib.AlgebraicGeometry.Scheme.Morphism.QuasiCompact.Descent
import StacksCheckRecall

open CategoryTheory.Limits
open AlgebraicGeometry

universe u

/- Lemma 29.23.6: let `f : X ⟶ Y` be a morphism of schemes and let `g : Y' ⟶ Y` be open and
surjective. If the base change `pullback.snd f g : pullback f g ⟶ Y'` is quasi-compact, then `f`
is quasi-compact. -/
@[stacks 04ZE] #check
  (AlgebraicGeometry.QuasiCompact.of_isOpenMap_of_surjective_baseChange :
    ∀ {X Y Y' : Scheme.{u}} (f : X ⟶ Y) (g : Y' ⟶ Y) [Surjective g],
      IsOpenMap g.base → QuasiCompact (pullback.snd f g) → QuasiCompact f)
