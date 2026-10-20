/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.AlgebraicGeometry.Scheme.Morphism.FiberCycleFamily.ClosedSubscheme
public import ReasLib.AlgebraicGeometry.Scheme.Morphism.FiberCycleFamily.Operations

/-!
# Compatibility of associated closed-subscheme cycle families

The associated fibrewise cycle family of a closed subscheme of bounded fibre
dimension commutes with base change, restriction, and flat pullback.
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry

noncomputable section

universe u

namespace AlgebraicGeometry.Scheme.Hom

/-- The fibrewise dimension bound of a closed subscheme is preserved by inverse
image along a cartesian square. -/
theorem fiberClosedSubschemeDimensionLE_baseChange
    {S X S' X' : Scheme.{u}} {f : X ⟶ S} {g : S' ⟶ S} {g' : X' ⟶ X} {f' : X' ⟶ S'}
    [LocallyOfFiniteType f] [LocallyOfFiniteType f'] (hpb : IsPullback g' f' f g)
    (Z : X.IdealSheafData) (r : ℕ) (hZ : f.fiberClosedSubschemeDimensionLE Z r) :
    f'.fiberClosedSubschemeDimensionLE (Z.comap g') r := sorry

/-- The associated fibrewise cycle family of a closed subscheme
of fibre dimension at most `r` commutes with base change along a cartesian
square. -/
theorem closedSubschemeFiberCycleFamily_baseChange
    {S X S' X' : Scheme.{u}} {f : X ⟶ S} {g : S' ⟶ S} {g' : X' ⟶ X} {f' : X' ⟶ S'}
    [LocallyOfFiniteType f] [LocallyOfFiniteType f'] (hpb : IsPullback g' f' f g)
    (Z : X.IdealSheafData) (r : ℕ) (hZ : f.fiberClosedSubschemeDimensionLE Z r) :
    FiberCycleFamily.baseChange hpb (closedSubschemeFiberCycleFamily f Z r hZ) =
      closedSubschemeFiberCycleFamily f' (Z.comap g') r
        (fiberClosedSubschemeDimensionLE_baseChange hpb Z r hZ) := sorry

/-- The fibrewise dimension bound of a closed subscheme is preserved by
restriction to compatible opens. -/
theorem fiberClosedSubschemeDimensionLE_restrict
    {X S : Scheme.{u}} {f : X ⟶ S} [LocallyOfFiniteType f]
    (U : X.Opens) (V : S.Opens) (hU : U ≤ f ⁻¹ᵁ V) (Z : X.IdealSheafData) (r : ℕ)
    (hZ : f.fiberClosedSubschemeDimensionLE Z r) :
    (f.resLE V U hU).fiberClosedSubschemeDimensionLE (Z.comap U.ι) r := sorry

/-- The associated fibrewise cycle family of a closed subscheme
of fibre dimension at most `r` commutes with restriction to compatible opens. -/
theorem closedSubschemeFiberCycleFamily_restrict
    {X S : Scheme.{u}} {f : X ⟶ S} [LocallyOfFiniteType f]
    (U : X.Opens) (V : S.Opens) (hU : U ≤ f ⁻¹ᵁ V) (Z : X.IdealSheafData) (r : ℕ)
    (hZ : f.fiberClosedSubschemeDimensionLE Z r) :
    FiberCycleFamily.restrict U V hU (closedSubschemeFiberCycleFamily f Z r hZ) =
      closedSubschemeFiberCycleFamily (f.resLE V U hU) (Z.comap U.ι) r
        (fiberClosedSubschemeDimensionLE_restrict U V hU Z r hZ) := sorry

/-- The fibrewise dimension bound of a closed subscheme is preserved by flat
pullback of relative dimension `e`, with the bound shifted by `e`. -/
theorem fiberClosedSubschemeDimensionLE_flatPullback
    {X' X S : Scheme.{u}} {f : X ⟶ S} {f' : X' ⟶ S}
    [LocallyOfFiniteType f] [LocallyOfFiniteType f'] (h : X' ⟶ X)
    (hf : h ≫ f = f') (e : ℕ) [Flat h] [RelativeDimension h e]
    (Z : X.IdealSheafData) (r : ℕ) (hZ : f.fiberClosedSubschemeDimensionLE Z r) :
    f'.fiberClosedSubschemeDimensionLE (Z.comap h) (r + e) := sorry

/-- The associated fibrewise cycle family of a closed subscheme
of fibre dimension at most `r` commutes with flat pullback of relative dimension
`e`. -/
theorem closedSubschemeFiberCycleFamily_flatPullback
    {X' X S : Scheme.{u}} {f : X ⟶ S} {f' : X' ⟶ S}
    [LocallyOfFiniteType f] [LocallyOfFiniteType f'] (h : X' ⟶ X)
    (hf : h ≫ f = f') (e : ℕ) [Flat h] [RelativeDimension h e]
    (Z : X.IdealSheafData) (r : ℕ) (hZ : f.fiberClosedSubschemeDimensionLE Z r) :
    FiberCycleFamily.flatPullback h hf e (closedSubschemeFiberCycleFamily f Z r hZ) =
      FiberCycleFamily.reindex (Int.natCast_add r e)
        (closedSubschemeFiberCycleFamily f' (Z.comap h) (r + e)
          (fiberClosedSubschemeDimensionLE_flatPullback h hf e Z r hZ)) := sorry

end AlgebraicGeometry.Scheme.Hom
