/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.AlgebraicGeometry.AlgebraicSpace.Cover.Fppf.Cech
import StacksCheckRecall

open CategoryTheory AlgebraicGeometry

universe u

/- Lemma 73.8.10: let `S` be a scheme and let `X` be an algebraic space over
`S`. Let `P` be a property of objects of `(Spaces / X)_fppf`, identified with
objects of `Over X`, such that whenever `{Uᵢ ⟶ U}` is a covering in this slice
(an `FppfCovering` family of morphisms in `Over X`), if `P` holds on every
Čech fibre product `U_{i₀} ×_U ⋯ ×_U U_{iₚ}` then `P` holds on `U`. If `P`
holds for every object that is affine and flat and locally of finite
presentation over `X`, then `P` holds on `Over.mk (𝟙 X)`. -/
@[stacks 0DK6] #check (AlgebraicGeometry.AlgebraicSpace.Fppf.cechEnough :
  ∀ {S : Scheme.{u}} {X : AlgebraicSpace S} (P : ObjectProperty (Over X))
    (h_cech : AlgebraicGeometry.AlgebraicSpace.Fppf.IsStableUnderCech.{u, u} P)
    (h_affine : ∀ (U : Over X) [AlgebraicGeometry.AlgebraicSpace.IsAffine U.left]
      [AlgebraicGeometry.AlgebraicSpace.Flat U.hom]
      [AlgebraicGeometry.AlgebraicSpace.LocallyOfFinitePresentation U.hom], P U),
    P (Over.mk (𝟙 X)))
