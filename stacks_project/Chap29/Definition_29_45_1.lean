/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.AlgebraicGeometry.Scheme.Morphism.UniversalHomeomorphism
import StacksCheckRecall

@[expose] public section

open CategoryTheory CategoryTheory.MorphismProperty

universe u

/-!
# Definition 29.45.1

This chapter entry is a source-facing recall of the neutral universal-homeomorphism API in
`ReasLib.AlgebraicGeometry.Scheme.Morphism.UniversalHomeomorphism`.
-/

/- Definition 29.45.1: A scheme morphism is a universal homeomorphism exactly when every base
change induces a homeomorphism on underlying spaces. -/
@[stacks 04DD] #check (AlgebraicGeometry.universalHomeomorphism_iff :
  ∀ {X Y : AlgebraicGeometry.Scheme.{u}} (f : X ⟶ Y),
    AlgebraicGeometry.UniversalHomeomorphism f ↔
      universally AlgebraicGeometry.topologicallyIsHomeomorph f)

#check @AlgebraicGeometry.topologicallyIsHomeomorph
#check @AlgebraicGeometry.UniversalHomeomorphism
#check @AlgebraicGeometry.UniversalHomeomorphism.pullbackSnd_isHomeomorph
#check @AlgebraicGeometry.Scheme.Hom.isHomeomorph
#check @AlgebraicGeometry.UniversalHomeomorphism.comp
#check @AlgebraicGeometry.UniversalHomeomorphism.pullback_snd
