/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.AlgebraicGeometry.Scheme.Module.Derived.Quasicoherent.Pushforward.CohomologicalDimension
public import ReasLib.AlgebraicGeometry.Scheme.Module.Derived.Quasicoherent.CohomologyIn

@[expose] public section

open AlgebraicGeometry CategoryTheory

universe u

namespace AlgebraicGeometry.Scheme.DerivedQCoh

/-- A right adjoint to derived quasicoherent pushforward along a morphism of
quasi-compact quasi-separated schemes preserves lower cohomological bounds up to a
uniform integer shift. -/
theorem rightAdjoint_uniformLowerBound :
    ∀ {X Y : Scheme.{u}}
      [CompactSpace X] [QuasiSeparatedSpace X] [CompactSpace Y] [QuasiSeparatedSpace Y]
      (f : X ⟶ Y) (a : DerivedQCoh Y ⥤ DerivedQCoh X)
      (adj : pushforwardCohomologyIn f ⊣ a),
      ∃ N : ℤ, ∀ (K : DerivedQCoh Y) (c : ℤ),
        K.obj.IsGE (c + 1) → (a.obj K).obj.IsGE (c - N + 1) := sorry

end AlgebraicGeometry.Scheme.DerivedQCoh
