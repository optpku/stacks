/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

import ReasLib.AlgebraicGeometry.Scheme.Morphism.Projective.QuasiProjective.BaseChange
import StacksCheckRecall

open AlgebraicGeometry
open CategoryTheory CategoryTheory.Limits
open scoped AlgebraicGeometry

universe u

/- Lemma 29.40.2: A base change of a quasi-projective morphism is quasi-projective. -/
@[stacks 0B3G] #check
  (AlgebraicGeometry.QuasiProjective.pullback_snd :
    ∀ {X S S' : Scheme.{u}} {f : X ⟶ S},
      AlgebraicGeometry.QuasiProjective f →
        ∀ g : S' ⟶ S,
          AlgebraicGeometry.QuasiProjective (pullback.snd f g))
