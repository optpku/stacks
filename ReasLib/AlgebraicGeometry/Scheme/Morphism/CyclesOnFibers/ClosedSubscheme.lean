/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import Mathlib.AlgebraicGeometry.Morphisms.Flat
public import ReasLib.AlgebraicGeometry.Scheme.Morphism.FiberCycleFamily.ClosedSubscheme
public import ReasLib.AlgebraicGeometry.Scheme.Morphism.CyclesOnFibers.Cap

/-!
# Closed-subscheme fibre-cycle actions

The fibre-cycle family of a closed subscheme flat over the base acts on a
closed-subscheme cycle by taking the associated cycle of the scheme-theoretic
fibre product.
-/

@[expose] public section

open AlgebraicGeometry CategoryTheory

noncomputable section

universe u

namespace AlgebraicGeometry.Scheme.Hom
namespace CyclesOnFibers

/-- If `Z` has fibre dimension at most `r` over `Y` and `W` has `δ`-dimension
at most `e`, then the closed subscheme `Z ⊔ W.comap f`, representing the
scheme-theoretic fibre product `Z ×_Y W` inside `X`, has `δ`-dimension at most
`(r : ℤ) + e`. -/
theorem closedSubschemeDeltaDimension_sup_comap_le {S X Y : Scheme.{u}}
    [UniversallyCatenary S] (p : Y ⟶ S) (f : X ⟶ Y)
    [LocallyOfFiniteType p] [LocallyOfFiniteType f] [LocallyOfFiniteType (f ≫ p)]
    (δ : S → ℤ) [IsDimensionFunction δ]
    (Z : X.IdealSheafData) (r : ℕ) (hZ : f.fiberClosedSubschemeDimensionLE Z r)
    (W : Y.IdealSheafData) (e : ℤ)
    (hW : p.closedSubschemeDeltaDimension δ W ≤ (e : EInt)) :
    (f ≫ p).closedSubschemeDeltaDimension δ (Z ⊔ W.comap f) ≤
      ((r : ℤ) + e : EInt) :=
  sorry

/-- For a closed subscheme `Z` flat over `Y` with fibre dimension at most `r`,
the associated fibre-cycle family acts on the degree-`e` associated cycle of
a closed subscheme `W` of `δ`-dimension at most `e` to give the degree-`r + e`
associated cycle of the scheme-theoretic fibre product `Z ×_Y W`. -/
theorem cap_closedSubschemeFiberCycleFamily {S X Y : Scheme.{u}}
    [UniversallyCatenary S] (p : Y ⟶ S) (f : X ⟶ Y)
    [LocallyOfFiniteType p] [LocallyOfFiniteType f] [LocallyOfFiniteType (f ≫ p)]
    (δ : S → ℤ) [IsDimensionFunction δ]
    (Z : X.IdealSheafData) (r : ℕ) (hZ : f.fiberClosedSubschemeDimensionLE Z r)
    (W : Y.IdealSheafData) (e : ℤ)
    (hW : p.closedSubschemeDeltaDimension δ W ≤ (e : EInt))
    [Flat (Z.subschemeι ≫ f)] :
    cap p f δ (closedSubschemeFiberCycleFamily f Z r hZ)
        (p.closedSubschemeCycle δ W e hW) =
      (f ≫ p).closedSubschemeCycle δ (Z ⊔ W.comap f) ((r : ℤ) + e)
        (closedSubschemeDeltaDimension_sup_comap_le p f δ Z r hZ W e hW) :=
  sorry

/-- At every point of `X`, the coefficient of the action of a flat closed
subscheme's fibre-cycle family on a closed-subscheme cycle equals the coefficient
of the associated cycle of their scheme-theoretic fibre product. -/
theorem cap_closedSubschemeFiberCycleFamily_apply {S X Y : Scheme.{u}}
    [UniversallyCatenary S] (p : Y ⟶ S) (f : X ⟶ Y)
    [LocallyOfFiniteType p] [LocallyOfFiniteType f] [LocallyOfFiniteType (f ≫ p)]
    (δ : S → ℤ) [IsDimensionFunction δ]
    (Z : X.IdealSheafData) (r : ℕ) (hZ : f.fiberClosedSubschemeDimensionLE Z r)
    (W : Y.IdealSheafData) (e : ℤ)
    (hW : p.closedSubschemeDeltaDimension δ W ≤ (e : EInt))
    [Flat (Z.subschemeι ≫ f)] (x : X) :
    CycleGroup.toAlgebraicCycle ((f ≫ p).relativeDimensionFunction δ)
        ((r : ℤ) + e)
        (cap p f δ (closedSubschemeFiberCycleFamily f Z r hZ)
          (p.closedSubschemeCycle δ W e hW)) x =
      CycleGroup.toAlgebraicCycle ((f ≫ p).relativeDimensionFunction δ)
        ((r : ℤ) + e)
        ((f ≫ p).closedSubschemeCycle δ (Z ⊔ W.comap f) ((r : ℤ) + e)
          (closedSubschemeDeltaDimension_sup_comap_le p f δ Z r hZ W e hW)) x :=
  sorry

end CyclesOnFibers
end AlgebraicGeometry.Scheme.Hom
