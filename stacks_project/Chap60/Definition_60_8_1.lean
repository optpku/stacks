/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.AlgebraicGeometry.Crystalline.Object
import ReasLib.AlgebraicGeometry.Crystalline.Base
import StacksCheckRecall

@[expose] public section

open AlgebraicGeometry CategoryTheory

universe u

variable {p : ℕ} [Fact p.Prime]
variable (B : AlgebraicGeometry.Scheme.Crystalline.Base.{u} p)

/- Definition 60.8.1: in Situation 60.7.5, `RelativeCRIS` is the category
   `CRIS(X/S, I, γ)` of divided-power thickenings over the fixed base equipped
   with an S-morphism from their source to X, with compatible-square morphisms
   preserving the divided powers. -/
@[stacks 07I6] #check (RelativeCRIS B.scheme B.ideal B.dividedPowers B.compatible
  B.source B.sourceToClosed : CategoryTheory.Cat.{u, u + 1})
