/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

import StacksCheckRecall

public import ReasLib.AlgebraicGeometry.AlgebraicSpace.CompletionAlong.RigSurjective
public import stacks_project.Chap66.Definition_66_24_1_Noetherian
public import stacks_project.Chap67.Definition_67_5_2_Surjective
public import stacks_project.Chap67.Definition_67_40_1_Proper
public import stacks_project.Chap67.Lemma_67_17_2_InverseImage
public import stacks_project.Chap67.Remark_67_12_5_Opens
public import stacks_project.Chap88.Definition_88_21_1
public import stacks_project.Chap88.Lemma_88_23_1

/-!
# Proper surjective morphisms of completions

If a morphism of algebraic spaces is proper, the source is completed along the
closed preimage of a closed subset, and the comparison of open complements is
surjective, then the induced morphism of formal completions is rig-surjective.
-/

@[expose] public section

open CategoryTheory AlgebraicGeometry AlgebraicGeometry.AlgebraicSpace
open TopologicalSpace

noncomputable section

universe u

namespace AlgebraicGeometry.AlgebraicSpace

/- Lemma 88.23.10: if `X` is locally Noetherian, `f : X' ⟶ X` is proper, and
every point outside `T` has a preimage under `Points.map f`, equivalently the
comparison of open complements is surjective, then `completionAlong.map f T`
is rig-surjective. -/
@[stacks 0AQW] #check
  (AlgebraicGeometry.AlgebraicSpace.rigSurjective_completionAlongMap :
    ∀ {S : Scheme.{u}}
    {X X' : AlgebraicSpace S} [IsLocallyNoetherian X] (f : X' ⟶ X)
    [Proper f] (T : Closeds (Points X))
    (h_surj : ∀ x : Points X, x ∉ (T : Set (Points X)) →
      ∃ x' : Points X', Points.map f x' = x),
    FormalAlgebraicSpace.RigSurjective (completionAlong.map f T))

end AlgebraicGeometry.AlgebraicSpace
