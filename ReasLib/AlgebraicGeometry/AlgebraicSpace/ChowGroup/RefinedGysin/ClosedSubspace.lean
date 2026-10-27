/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.AlgebraicGeometry.AlgebraicSpace.ChowGroup.RefinedGysin
public import ReasLib.AlgebraicGeometry.AlgebraicSpace.ClosedSubspace.AssociatedCycle
public import ReasLib.AlgebraicGeometry.AlgebraicSpace.Closed.InverseImage

/-! # Refined Gysin maps on closed-subspace cycles -/

@[expose] public section

open CategoryTheory CategoryTheory.MonoidalCategory
open AlgebraicGeometry AlgebraicGeometry.AlgebraicSpace

noncomputable section

universe u

namespace AlgebraicGeometry.AlgebraicSpace.Hom

variable {S : Scheme.{u}} {B X : AlgebraicSpace S}
  [UniversallyCatenary B] [IsQuasiSeparated B]
  (f : X ⟶ B) [QuasiSeparated f] [LocallyOfFiniteType f]
  (δ : Points B → ℤ) [IsDimensionFunction δ]

/-- If a closed subspace has relative dimension at most `k + 1` and its
intersection with the zero scheme of an invertible-module section is an
effective Cartier divisor on it, the degree-`k` associated intersection cycle
belongs to the degree-`k` cycle group of the zero scheme. -/
theorem associatedCycle_inverseImage_mem (L : X.Modules) [isInvertibleObject L]
    (s : L.sections) (Z : ClosedSubspace X) (k : ℤ)
    (hZ : closedSubspaceDeltaDimension f δ Z ≤ ((k + 1 : ℤ) : EInt))
    [IsEffectiveCartierDivisor ((zeroScheme L s).inverseImageSubspace Z.ι).ι] :
    @ClosedSubspace.associatedCycle S (zeroScheme L s).X
        (LocallyOfFiniteType.isLocallyNoetherian (zeroSchemeι L s ≫ f))
        (Z.inverseImageSubspace (zeroSchemeι L s))
        (relativeDimensionFunction (zeroSchemeι L s ≫ f) δ) k ∈
      cycleGroup (zeroSchemeι L s ≫ f) δ k :=
  sorry

/-- Refined intersection of the degree-`k + 1` cycle of a dimension-bounded
closed subspace is its degree-`k` intersection cycle on the zero scheme, when
the intersection is an effective Cartier divisor on the closed subspace. -/
theorem gysinCycle_closedSubspaceCycle (L : X.Modules) [isInvertibleObject L]
    (s : L.sections) (Z : ClosedSubspace X) (k : ℤ)
    (hZ : closedSubspaceDeltaDimension f δ Z ≤ ((k + 1 : ℤ) : EInt))
    [IsEffectiveCartierDivisor ((zeroScheme L s).inverseImageSubspace Z.ι).ι] :
    ChowGroup.RefinedGysin.cycle f δ L s k (closedSubspaceCycle f δ Z (k + 1) hZ) =
      @ClosedSubspace.associatedCycle S (zeroScheme L s).X
        (LocallyOfFiniteType.isLocallyNoetherian (zeroSchemeι L s ≫ f))
        (Z.inverseImageSubspace (zeroSchemeι L s))
        (relativeDimensionFunction (zeroSchemeι L s ≫ f) δ) k := by
  have hmem := associatedCycle_inverseImage_mem f δ L s Z k hZ
  sorry

/-- Refined Gysin sends the cycle of a dimension-bounded closed subspace to
the Chow class of its intersection cycle on the zero scheme of the section,
provided the intersection is an effective Cartier divisor on the subspace. -/
theorem gysin_closedSubspaceCycle (L : X.Modules) [isInvertibleObject L]
    (s : L.sections) (Z : ClosedSubspace X) (k : ℤ)
    (hZ : closedSubspaceDeltaDimension f δ Z ≤ ((k + 1 : ℤ) : EInt))
    [IsEffectiveCartierDivisor ((zeroScheme L s).inverseImageSubspace Z.ι).ι] :
    gysin f δ k L s
        ⟨closedSubspaceCycle f δ Z (k + 1) hZ,
          closedSubspaceCycle_mem_cycleGroup f δ Z (k + 1) hZ⟩ =
      chowMk (zeroSchemeι L s ≫ f) δ k
        ⟨@ClosedSubspace.associatedCycle S (zeroScheme L s).X
            (LocallyOfFiniteType.isLocallyNoetherian (zeroSchemeι L s ≫ f))
            (Z.inverseImageSubspace (zeroSchemeι L s))
            (relativeDimensionFunction (zeroSchemeι L s ≫ f) δ) k,
          associatedCycle_inverseImage_mem f δ L s Z k hZ⟩ := by
  have hcycle := gysinCycle_closedSubspaceCycle f δ L s Z k hZ
  sorry

end AlgebraicGeometry.AlgebraicSpace.Hom
