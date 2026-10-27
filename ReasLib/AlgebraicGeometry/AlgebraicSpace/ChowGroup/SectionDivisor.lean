/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.AlgebraicGeometry.AlgebraicSpace.CycleGroup.SectionDivisor
public import ReasLib.AlgebraicGeometry.AlgebraicSpace.ChowGroup.FirstChernFundamental

/-!
# Zero-subspace cycles and first Chern classes

For a nonzero global section of an invertible module on a good integral
algebraic space, the Chow class of its zero subspace is the first Chern class
capped with the fundamental cycle.
-/

@[expose] public section

open CategoryTheory AlgebraicGeometry AlgebraicGeometry.AlgebraicSpace
open CategoryTheory.MonoidalCategory

noncomputable section

universe u

namespace AlgebraicGeometry.AlgebraicSpace.Hom

variable {S : Scheme.{u}} {B X : AlgebraicSpace S}
  [UniversallyCatenary B] [IsAbsolutelyQuasiSeparated B]
variable (f : X ⟶ B) [QuasiSeparated f] [LocallyOfFiniteType f]
variable (δ : Points B → ℤ) [IsDimensionFunction δ]
variable [IsIntegral X]

/-- The first Chern class of an invertible module capped with the fundamental
cycle of a good integral algebraic space equals the Chow class of the
zero-subspace cycle of any nonzero global section. -/
theorem firstChernCapFundamental_eq_zeroSchemeCycle
    {L : X.Modules} [isInvertibleObject L] (s : L.sections) (hs : s ≠ 0) :
    firstChernCapFundamental f δ L =
      chowClass f δ
        (@ClosedSubspace.associatedCycle S X (LocallyOfFiniteType.isLocallyNoetherian f)
          (zeroScheme L s) (relativeDimensionFunction f δ)
          (deltaDimension f δ (univIrreducibleClosed X) - 1)) := sorry

end AlgebraicGeometry.AlgebraicSpace.Hom
