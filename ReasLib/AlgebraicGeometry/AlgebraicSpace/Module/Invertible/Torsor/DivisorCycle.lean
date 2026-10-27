/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.AlgebraicGeometry.AlgebraicSpace.Module.Invertible.Torsor.Integral
public import ReasLib.AlgebraicGeometry.AlgebraicSpace.Module.Invertible.Torsor.MeromorphicSection
public import ReasLib.AlgebraicGeometry.AlgebraicSpace.CycleGroup.FlatPullback
public import ReasLib.AlgebraicGeometry.AlgebraicSpace.CycleGroup.WeilDivisor
public import ReasLib.AlgebraicGeometry.AlgebraicSpace.Separation.Absolute.Relative

/-! # Divisor cycles on multiplicative torsors -/

@[expose] public section

open CategoryTheory CategoryTheory.MonoidalCategory

noncomputable section

universe u

namespace AlgebraicGeometry.AlgebraicSpace

/-- For a good integral algebraic space over an absolutely quasi-separated,
universally catenary base with a dimension function, flat pullback of the divisor
cycle of a regular meromorphic section of an invertible module to its
multiplicative torsor is the divisor cycle of the meromorphic function obtained
through the tautological trivialization. -/
@[stacks 0EQH]
theorem gmTorsorπ_meromorphicSectionDivisorCycle {S : Scheme.{u}}
    {B X : AlgebraicSpace S} [UniversallyCatenary B] [IsAbsolutelyQuasiSeparated B]
    (f : X ⟶ B) [QuasiSeparated f] [LocallyOfFiniteType f]
    (δ : Points B → ℤ) [IsDimensionFunction δ] [IsIntegral X]
    (L : X.Modules) [isInvertibleObject L] (s : meromorphicSections X L)
    (hs : IsRegularMeromorphicSection X L s) :
    Hom.flatPullback f (Modules.gmTorsorπ L ≫ f) δ (Modules.gmTorsorπ L) 1 rfl
        (Hom.deltaDimension f δ (univIrreducibleClosed X) - 1)
        (Hom.meromorphicSectionDivisorCycle f δ s hs) =
      Hom.meromorphicSectionDivisorCycle (Modules.gmTorsorπ L ≫ f) δ
        (gmTorsorTrivMeromorphicSection L s)
        (isRegularMeromorphicSection_gmTorsorTriv L s hs) :=
  sorry

end AlgebraicGeometry.AlgebraicSpace
