/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.AlgebraicGeometry.AlgebraicSpace.Module.Derived.TorDimension.Local
public import ReasLib.AlgebraicGeometry.AlgebraicSpace.Cover.Fpqc
public import ReasLib.AlgebraicGeometry.AlgebraicSpace.Pullback
public import ReasLib.AlgebraicGeometry.AlgebraicSpace.Module.Derived.Pullback

/-! # Fpqc descent of relative Tor dimension on algebraic spaces -/

@[expose] public section

open AlgebraicGeometry AlgebraicSpace CategoryTheory

universe u v

namespace AlgebraicGeometry.AlgebraicSpace.ModuleDerived

/-- Relative Tor-amplitude in any fixed integer interval can be checked after derived
pullback along an fpqc covering of the base, for complexes with quasi-coherent cohomology. -/
theorem hasTorAmplitudeInOver_iff_fpqcCovering
    {S : Scheme.{u}} {X Y : AlgebraicSpace S} {ι : Type v}
    (f : X ⟶ Y) (family : ι → Over Y) (hfamily : FpqcCovering family)
    (E : ModuleDerived X) (hE : derivedQuasiCoherentModuleProperty X E)
    (a b : ℤ) :
    HasTorAmplitudeInOver f E a b ↔
      ∀ i, HasTorAmplitudeInOver (overPullbackFst f (family i))
        ((modulePullbackDerived (overPullbackSnd f (family i))).obj E) a b := sorry

/-- Locally finite relative Tor dimension can be checked after derived pullback along an
fpqc covering of the base, for complexes with quasi-coherent cohomology. -/
theorem locallyFiniteTorDimensionOver_iff_fpqcCovering
    {S : Scheme.{u}} {X Y : AlgebraicSpace S} {ι : Type v}
    (f : X ⟶ Y) (family : ι → Over Y) (hfamily : FpqcCovering family)
    (E : ModuleDerived X) (hE : derivedQuasiCoherentModuleProperty X E) :
    locallyFiniteTorDimensionOver f E ↔
      ∀ i, locallyFiniteTorDimensionOver (overPullbackFst f (family i))
        ((modulePullbackDerived (overPullbackSnd f (family i))).obj E) := sorry

end AlgebraicGeometry.AlgebraicSpace.ModuleDerived
