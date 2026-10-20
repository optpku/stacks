/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import stacks_project.Chap65.Lemma_65_12_4_Immersion
public import stacks_project.Chap67.Definition_67_8_2_QuasiCompact
public import ReasLib.AlgebraicGeometry.AlgebraicSpace.Morphism.ClosedImmersion.QuasiCompact
import StacksCheckRecall

/-!
# Closed immersions of algebraic spaces are quasi-compact

A closed immersion of algebraic spaces over a scheme `S` is quasi-compact in
the sense of Definition 67.8.2.
-/

@[expose] public section

open CategoryTheory AlgebraicGeometry

universe u

namespace AlgebraicGeometry.AlgebraicSpace

/- Lemma 67.13.3: A closed immersion of algebraic spaces is quasi-compact. -/
@[stacks 04CG] #check
  (AlgebraicGeometry.AlgebraicSpace.IsClosedImmersion.quasiCompact :
    ∀ {S : Scheme.{u}} {X Y : AlgebraicSpace S} (f : X ⟶ Y) [IsClosedImmersion f],
      QuasiCompact f)

#check (AlgebraicGeometry.AlgebraicSpace.IsClosedImmersion.le_quasiCompact :
  ∀ {S : Scheme.{u}},
    (@IsClosedImmersion S : MorphismProperty (AlgebraicSpace S)) ≤
      (@QuasiCompact S : MorphismProperty (AlgebraicSpace S)))

end AlgebraicGeometry.AlgebraicSpace
