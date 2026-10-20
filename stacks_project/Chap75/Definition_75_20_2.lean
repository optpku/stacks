/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import stacks_project.Chap75.Definition_75_20_2_TorIndependence
import StacksCheckRecall

universe u

variable {S : AlgebraicGeometry.Scheme.{u}} {B : AlgebraicGeometry.AlgebraicSpace S}

/- Definition 75.20.2: let `S` be a scheme, let `B` be an algebraic space over `S`, and let
`X` and `Y` be algebraic spaces over `B`. They are Tor independent over `B` if, for every
commutative diagram of geometric points `Spec(k) ⟶ X`, `Spec(k) ⟶ Y`, and `Spec(k) ⟶ B`,
the étale local rings `𝒪_{X, x̄}` and `𝒪_{Y, ȳ}` are Tor independent over `𝒪_{B, b̄}`. -/
@[stacks 08IP] #check (AlgebraicGeometry.AlgebraicSpace.TorIndependentOver :
  CategoryTheory.Over B → CategoryTheory.Over B → Prop)
