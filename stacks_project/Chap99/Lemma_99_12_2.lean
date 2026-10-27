/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

import StacksCheckRecall
public import ReasLib.AlgebraicGeometry.AlgebraicSpace.RelativeHom.GraphOpenImmersion

/-!
# Lemma 99.12.2

Under the standing hypotheses of Lemma 99.12.1, the graph transformation
`Mor_B(Z, X) ⟶ Hilb_{Z ×_B X / B}` is representable by open immersions.
-/

@[expose] public section

open CategoryTheory AlgebraicGeometry AlgebraicGeometry.AlgebraicSpace

noncomputable section

universe u

/- Lemma 99.12.2: under the standing hypotheses of Lemma 99.12.1, the graph
transformation is representable by open immersions. -/
@[stacks 0D1B] #check (AlgebraicGeometry.AlgebraicSpace.RelativeHom.graph_isOpenImmersion :
  ∀ {S : Scheme.{u}} {Z B X : AlgebraicSpace S} (z : Z ⟶ B) (x : X ⟶ B)
    [Separated x] [FinitePresentation z] [Flat z] [Proper z],
    MorphismProperty.relative uliftYoneda.{u + 1}
      (fun _ _ h ↦ AlgebraicGeometry.IsOpenImmersion h.left.left :
        MorphismProperty (SchemeOver B))
        (AlgebraicGeometry.AlgebraicSpace.RelativeHom.graph z x))
