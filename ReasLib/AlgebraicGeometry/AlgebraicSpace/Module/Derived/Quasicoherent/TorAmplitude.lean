/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.CategoryTheory.DerivedCategory.Monoidal.TorAmplitude
public import ReasLib.AlgebraicGeometry.AlgebraicSpace.Separation.Absolute
public import ReasLib.AlgebraicGeometry.AlgebraicSpace.Module.Derived.Tensor

@[expose] public section

open AlgebraicGeometry AlgebraicGeometry.AlgebraicSpace CategoryTheory Limits
open scoped CategoryTheory.DerivedCategory.DerivedTensor

noncomputable section

universe u

namespace AlgebraicGeometry.AlgebraicSpace.DerivedQCoh

/-- On an absolutely quasi-separated algebraic space, a derived module with
quasi-coherent cohomology has Tor-amplitude in `[a, b]` if and only if its derived
tensor product with every quasi-coherent module has vanishing cohomology outside
that interval. -/
theorem hasTorAmplitudeIn_iff_homology {S : Scheme.{u}} {X : AlgebraicSpace S}
    [IsAbsolutelyQuasiSeparated X] (E : DerivedQCoh X) (a b : ℤ) (hab : a ≤ b) :
    DerivedCategory.DerivedTensor.HasTorAmplitudeIn E.obj a b ↔
      ∀ (F : QCoh X) (i : ℤ), i ∉ Set.Icc a b →
        IsZero ((DerivedCategory.homologyFunctor (Modules X) i).obj
          (E.obj ⊗ᴸ (DerivedCategory.singleFunctor (Modules X) 0).obj F.obj)) :=
  sorry

end AlgebraicGeometry.AlgebraicSpace.DerivedQCoh
