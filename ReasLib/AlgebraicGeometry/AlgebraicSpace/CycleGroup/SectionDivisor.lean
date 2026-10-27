/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.AlgebraicGeometry.AlgebraicSpace.Module.Meromorphic.OfGlobal
public import ReasLib.AlgebraicGeometry.AlgebraicSpace.CycleGroup.WeilDivisor
public import ReasLib.AlgebraicGeometry.AlgebraicSpace.ClosedSubspace.AssociatedCycle
public import ReasLib.AlgebraicGeometry.AlgebraicSpace.ClosedSubspace.ZeroSection
public import ReasLib.AlgebraicGeometry.AlgebraicSpace.Separation.Absolute.Relative

/-!
# Divisor cycles of global sections

On a good integral algebraic space, the zero subspace of a nonzero global
section of an invertible module computes its divisor cycle, including the
scheme-theoretic multiplicities, for an integer-valued dimension function.
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

/-- The zero-scheme cycle of a nonzero section has degree `dim_δ(X) - 1`. -/
theorem zeroSchemeCycle_mem {L : X.Modules} [isInvertibleObject L]
    (s : L.sections) (hs : s ≠ 0) :
    @ClosedSubspace.associatedCycle S X (LocallyOfFiniteType.isLocallyNoetherian f)
        (zeroScheme L s) (relativeDimensionFunction f δ)
        (deltaDimension f δ (univIrreducibleClosed X) - 1) ∈
      cycleGroup f δ (deltaDimension f δ (univIrreducibleClosed X) - 1) := sorry

/-- The divisor cycle of the meromorphic image of a nonzero global section of
an invertible module on a good integral algebraic space is the associated
cycle of its zero subspace in degree one less than the dimension. -/
theorem meromorphicSectionDivisorCycle_eq_zeroSchemeCycle
    {L : X.Modules} [isInvertibleObject L] (s : L.sections) (hs : s ≠ 0) :
    meromorphicSectionDivisorCycle f δ (toMeromorphicSection s)
        (@toMeromorphicSection_isRegular S X
          (LocallyOfFiniteType.isLocallyNoetherian f) inferInstance L inferInstance s hs) =
      @ClosedSubspace.associatedCycle S X (LocallyOfFiniteType.isLocallyNoetherian f)
        (zeroScheme L s) (relativeDimensionFunction f δ)
        (deltaDimension f δ (univIrreducibleClosed X) - 1) := sorry

end AlgebraicGeometry.AlgebraicSpace.Hom
