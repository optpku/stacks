/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.AlgebraicGeometry.AlgebraicSpace.Module.Derived.RelativeDualizing
import StacksCheckRecall

@[expose] public section

open CategoryTheory AlgebraicGeometry.AlgebraicSpace

universe u

/- Definition 86.9.1: let `S` be a scheme and let `f : X ⟶ Y` be a proper, flat morphism
of algebraic spaces over `S` which is of finite presentation. A relative dualizing complex
for `X / Y` is a pair `(ω, τ)` consisting of a `Y`-perfect object `ω` of `D(𝒪_X)` and a
map `τ : Rf_* ω ⟶ 𝒪_Y` such that for any cartesian square with `Y'` an affine scheme the
pair `(L(g')^* ω, Lg^* τ)` is isomorphic to the twisted-inverse pair
`(a'(𝒪_{Y'}), Tr_{f', 𝒪_{Y'}})`. -/
@[stacks 0E5X] #check (AlgebraicGeometry.AlgebraicSpace.RelativeDualizingComplex :
  ∀ {S : AlgebraicGeometry.Scheme.{u}} {X Y : AlgebraicGeometry.AlgebraicSpace S}
    (f : X ⟶ Y), [AlgebraicGeometry.AlgebraicSpace.Proper f] →
    [AlgebraicGeometry.AlgebraicSpace.Flat f] →
    [AlgebraicGeometry.AlgebraicSpace.FinitePresentation f] → Type (u + 1))
