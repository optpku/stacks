/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

import StacksCheckRecall
import ReasLib.AlgebraicGeometry.Scheme.Module.Derived.PerfectApproximation

universe u

/- Definition 36.14.1: for a closed subset `T` of a scheme `X`, an object `E` of
`D_QCoh(𝒪_X)`, and `m : ℤ`, approximation holds when a perfect object `P` supported on `T`
maps to `E`, inducing cohomology isomorphisms in every degree `i` with `m < i` and an
epimorphism in degree `m`. -/
@[stacks 08EM] #check
  (AlgebraicGeometry.Scheme.HasPerfectApproximation :
    {X : AlgebraicGeometry.Scheme.{u}} →
      (T : TopologicalSpace.Closeds X) →
      (E : CategoryTheory.DerivedCategory.CohomologyIn
        (AlgebraicGeometry.RingedSpace.quasiCoherentModuleProperty X.toRingedSpace)) →
      (m : ℤ) → Prop)
