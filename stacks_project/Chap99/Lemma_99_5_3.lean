/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

import StacksCheckRecall
public import ReasLib.AlgebraicGeometry.AlgebraicSpace.CohStack.Isom

@[expose] public section

open CategoryTheory AlgebraicGeometry

universe u

/- Lemma 99.5.3: in Situation 99.5.1, with `𝒳 = CohStack f`, the diagonal
`Δ : 𝒳 ⟶ 𝒳 × 𝒳` is representable by algebraic spaces. At Hom-universe `u + 1`
this is the 94.10.11(1) condition that for every scheme `T` over `S` and
objects `x, y` of the fibre `𝒳_T`, the presheaf `Isom_𝒳(x, y)` is an algebraic
space over `T`. -/
@[stacks 08W6] #check
  (AlgebraicGeometry.AlgebraicSpace.CohStack.isom_isAlgebraicSpace :
    ∀ {S : Scheme.{u}} {X B : AlgebraicSpace S} (f : X ⟶ B),
      [AlgebraicSpace.FinitePresentation f] →
        AlgebraicGeometry.AlgebraicSpace.CohStack.isAlgebraicSpace f)
