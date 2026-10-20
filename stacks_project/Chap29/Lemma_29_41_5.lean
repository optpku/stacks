/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import Mathlib.AlgebraicGeometry.Morphisms.Proper
import StacksCheckRecall

@[expose] public section

-- Declarations for this item will be appended below by the statement pipeline.

open CategoryTheory.Limits

universe u

namespace AlgebraicGeometry

section

variable {X S S' : Scheme.{u}} (f : X ⟶ S) (g : S' ⟶ S)

/- Lemma 29.41.5: the base change of a proper morphism is proper, and the base change of a
universally closed morphism is universally closed. -/
@[stacks 01W4] #check
  (CategoryTheory.MorphismProperty.pullback_snd (P := @AlgebraicGeometry.IsProper) f g :
    AlgebraicGeometry.IsProper f →
      AlgebraicGeometry.IsProper (CategoryTheory.Limits.pullback.snd f g))

/- The base change of a universally closed morphism is universally closed. -/
#check
  (CategoryTheory.MorphismProperty.pullback_snd
      (P := @AlgebraicGeometry.UniversallyClosed) f g :
    AlgebraicGeometry.UniversallyClosed f →
      AlgebraicGeometry.UniversallyClosed (CategoryTheory.Limits.pullback.snd f g))

end

end AlgebraicGeometry
