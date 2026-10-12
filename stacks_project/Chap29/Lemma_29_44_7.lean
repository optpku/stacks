/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

import Mathlib.AlgebraicGeometry.Morphisms.Integral
import StacksCheckRecall

open CategoryTheory

universe u

/- Lemma 29.44.7: a morphism of schemes is integral if and only if it is affine and universally
closed. -/
@[stacks 01WM] #check
  (AlgebraicGeometry.IsIntegralHom.iff_universallyClosed_and_isAffineHom :
    ∀ {X S : AlgebraicGeometry.Scheme.{u}} {f : X ⟶ S},
      AlgebraicGeometry.IsIntegralHom f ↔
        AlgebraicGeometry.UniversallyClosed f ∧ AlgebraicGeometry.IsAffineHom f)
