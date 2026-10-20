/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.AlgebraicGeometry.AlgebraicSpace.Morphism.EtaleLocal
import StacksCheckRecall

@[expose] public section

universe u

/- Definition 67.22.2: let `S` be a scheme. Let `P` be a property of morphisms of
schemes which is étale local on the source-and-target. A morphism `f : X ⟶ Y` of
algebraic spaces over `S` has property `P` if the equivalent conditions of
Lemma 67.22.1 hold. Under this locality hypothesis, the definition uses the
universal condition of that lemma. -/
@[stacks 04RD] #check (AlgebraicGeometry.AlgebraicSpace.etaleLocal :
  ∀ {S : AlgebraicGeometry.Scheme.{u}}
    (P : CategoryTheory.MorphismProperty AlgebraicGeometry.Scheme.{u}),
    CategoryTheory.MorphismProperty (AlgebraicGeometry.AlgebraicSpace S))
