/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

import StacksCheckRecall
import ReasLib.AlgebraicGeometry.Scheme.DeRham.HodgeFiltration

universe u

/- Definition 50.7.1: for a morphism of schemes `f : X ⟶ S`, the Hodge filtration on
`Hⁿ_dR(X/S)` has stage
`FᵖHⁿ_dR(X/S) = image (Hⁿ(X, σ≥p Ωᵈᴿ[f]) ⟶ Hⁿ_dR(X/S))`, where `σ≥p` is the
brutal (stupid) truncation. -/
@[stacks 0FM8] #check
  (@AlgebraicGeometry.Scheme.DeRham.hodgeFiltration :
    {X S : AlgebraicGeometry.Scheme.{u}} →
      (f : X ⟶ S) → (n : ℤ) →
        CategoryTheory.DecreasingFiltration
          (AlgebraicGeometry.Scheme.DeRham.cohomology f n))
