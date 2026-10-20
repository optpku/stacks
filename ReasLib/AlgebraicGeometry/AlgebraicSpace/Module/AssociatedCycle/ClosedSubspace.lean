/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.AlgebraicGeometry.AlgebraicSpace.ClosedSubspace.AssociatedCycle
public import ReasLib.AlgebraicGeometry.AlgebraicSpace.Module.AssociatedCycle
public import ReasLib.AlgebraicGeometry.AlgebraicSpace.Module.Coherent.ClosedImmersion
public import ReasLib.AlgebraicGeometry.AlgebraicSpace.Separation.Absolute.Relative
public import ReasLib.AlgebraicGeometry.AlgebraicSpace.Module.Length.ClosedImmersion

/-!
# Cycles of closed subspaces and their structure modules

The cycle of a closed subspace agrees with the cycle of the direct image of its
structure module along the inclusion.
-/

@[expose] public section

open CategoryTheory AlgebraicGeometry AlgebraicGeometry.AlgebraicSpace

noncomputable section

universe u

namespace AlgebraicGeometry.AlgebraicSpace.Hom

/-- The support of the direct image of the structure module of a closed subspace
has relative dimension at most the dimension bound of that subspace. -/
theorem moduleSupportDeltaDimension_pushforward_unit_le
    {S : Scheme.{u}} {B X Z : AlgebraicSpace S} [UniversallyCatenary B]
    [IsAbsolutelyQuasiSeparated B] (f : X ⟶ B) [QuasiSeparated f] [LocallyOfFiniteType f]
    [IsLocallyNoetherian X] (δ : Points B → ℤ) [IsDimensionFunction δ]
    (i : Z ⟶ X) [IsClosedImmersion i] (k : ℤ)
    (hY : closedSubspaceDeltaDimension f δ (ClosedSubspace.ofι i) ≤ (k : EInt)) :
    moduleSupportDeltaDimension f δ (Modules.pushforwardStructureModule i) ≤
      (k : EInt) :=
  sorry

/-- For a closed subspace of relative dimension at most `k`, its degree-`k` cycle
equals that of the direct image of its structure module along the inclusion. -/
@[stacks 0EED]
theorem closedSubspaceCycle_eq_moduleCycle_pushforward_unit
    {S : Scheme.{u}} {B X Z : AlgebraicSpace S} [UniversallyCatenary B]
    [IsAbsolutelyQuasiSeparated B] (f : X ⟶ B) [QuasiSeparated f] [LocallyOfFiniteType f]
    [IsLocallyNoetherian X] (δ : Points B → ℤ) [IsDimensionFunction δ]
    (i : Z ⟶ X) [IsClosedImmersion i] (k : ℤ)
    (hY : closedSubspaceDeltaDimension f δ (ClosedSubspace.ofι i) ≤ (k : EInt)) :
    closedSubspaceCycle f δ (ClosedSubspace.ofι i) k hY =
      moduleCycle f δ (Modules.pushforwardStructureModule i) k
        (moduleSupportDeltaDimension_pushforward_unit_le f δ i k hY) :=
  sorry

end AlgebraicGeometry.AlgebraicSpace.Hom
