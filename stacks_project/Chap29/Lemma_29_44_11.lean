module

import Mathlib.AlgebraicGeometry.Morphisms.Proper
import StacksCheckRecall

open CategoryTheory

universe u

/- Lemma 29.44.11: a morphism of schemes is finite if and only if it is affine and proper. -/
@[stacks 01WN] #check
  (AlgebraicGeometry.IsFinite.iff_isProper_and_isAffineHom :
    ∀ {X S : AlgebraicGeometry.Scheme.{u}} {f : X ⟶ S},
      AlgebraicGeometry.IsFinite f ↔
        AlgebraicGeometry.IsProper f ∧ AlgebraicGeometry.IsAffineHom f)
