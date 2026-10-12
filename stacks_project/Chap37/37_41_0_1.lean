/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import ReasLib.AlgebraicGeometry.Scheme.Pullback.Opens
import StacksCheckRecall

@[expose] public section

open AlgebraicGeometry
open CategoryTheory Limits

universe u

/- 37.41.0.1: an open subscheme of a scheme pullback maps compatibly to the base. -/
@[stacks 02LJ] #check
  (AlgebraicGeometry.Scheme.Pullback.open_condition :
    ∀ {S X U : Scheme.{u}} (f : X ⟶ S) (φ : U ⟶ S)
      (V : (pullback f φ : Scheme).Opens),
      V.ι ≫ pullback.fst f φ ≫ f = V.ι ≫ pullback.snd f φ ≫ φ)
