/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.AlgebraicGeometry.AlgebraicSpace.Morphism.ClosedImmersion
public import stacks_project.Chap65.Lemma_65_12_4_Immersion
public import stacks_project.Chap67.Definition_67_45_2_Integral
import StacksCheckRecall

/-!
# Closed immersions of algebraic spaces are finite

A closed immersion of algebraic spaces over a scheme `S` is finite, and
therefore integral, in the sense of Definition 67.45.2.
-/

@[expose] public section

open CategoryTheory AlgebraicGeometry

universe u

namespace AlgebraicGeometry.AlgebraicSpace

/- Lemma 67.45.10 (1): A closed immersion of algebraic spaces is finite. -/
@[stacks 081Y] #check
  (AlgebraicGeometry.AlgebraicSpace.IsFinite.of_isClosedImmersion :
    ∀ {S : Scheme.{u}} {X Y : AlgebraicSpace S} (f : X ⟶ Y) [IsClosedImmersion f],
      IsFinite f)

/- Lemma 67.45.10 (2): A closed immersion of algebraic spaces is integral. -/
@[stacks 081Y] #check
  (AlgebraicGeometry.AlgebraicSpace.IsIntegralHom.of_isClosedImmersion :
    ∀ {S : Scheme.{u}} {X Y : AlgebraicSpace S} (f : X ⟶ Y) [IsClosedImmersion f],
      IsIntegralHom f)

end AlgebraicGeometry.AlgebraicSpace
