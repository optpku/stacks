/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.AlgebraicGeometry.Scheme.Morphism.FiberCycleFamily.ClosedSubscheme.Operations
import StacksCheckRecall

/-!
# Compatibility of associated closed-subscheme cycle families

The associated fibrewise cycle family of a closed subscheme of bounded fibre
dimension commutes with base change, restriction, and flat pullback.
-/

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry

universe u

namespace AlgebraicGeometry.Scheme.Hom

/- Lemma 62.5.5: the associated fibrewise cycle family of a closed subscheme
of fibre dimension at most `r` commutes with arbitrary cartesian base change. -/
@[stacks 0H4T]
#check (AlgebraicGeometry.Scheme.Hom.closedSubschemeFiberCycleFamily_baseChange :
    ∀
    {S X S' X' : Scheme.{u}} {f : X ⟶ S} {g : S' ⟶ S} {g' : X' ⟶ X} {f' : X' ⟶ S'}
    [LocallyOfFiniteType f] [LocallyOfFiniteType f'] (hpb : IsPullback g' f' f g)
    (Z : X.IdealSheafData) (r : ℕ) (hZ : f.fiberClosedSubschemeDimensionLE Z r),
    FiberCycleFamily.baseChange hpb (closedSubschemeFiberCycleFamily f Z r hZ) =
      closedSubschemeFiberCycleFamily f' (Z.comap g') r
        (fiberClosedSubschemeDimensionLE_baseChange hpb Z r hZ))

/- Lemma 62.5.5: the associated fibrewise cycle family of a closed subscheme
of fibre dimension at most `r` commutes with restriction to compatible opens. -/
@[stacks 0H4T]
#check (AlgebraicGeometry.Scheme.Hom.closedSubschemeFiberCycleFamily_restrict :
    ∀
    {X S : Scheme.{u}} {f : X ⟶ S} [LocallyOfFiniteType f]
    (U : X.Opens) (V : S.Opens) (hU : U ≤ f ⁻¹ᵁ V) (Z : X.IdealSheafData) (r : ℕ)
    (hZ : f.fiberClosedSubschemeDimensionLE Z r),
    FiberCycleFamily.restrict U V hU (closedSubschemeFiberCycleFamily f Z r hZ) =
      closedSubschemeFiberCycleFamily (f.resLE V U hU) (Z.comap U.ι) r
        (fiberClosedSubschemeDimensionLE_restrict U V hU Z r hZ))

/- Lemma 62.5.5: the associated fibrewise cycle family of a closed subscheme
of fibre dimension at most `r` commutes with flat pullback of relative dimension
`e`, shifting the dimension bound and cycle degree by `e`. -/
@[stacks 0H4T]
#check (AlgebraicGeometry.Scheme.Hom.closedSubschemeFiberCycleFamily_flatPullback :
    ∀
    {X' X S : Scheme.{u}} {f : X ⟶ S} {f' : X' ⟶ S}
    [LocallyOfFiniteType f] [LocallyOfFiniteType f'] (h : X' ⟶ X)
    (hf : h ≫ f = f') (e : ℕ) [Flat h] [RelativeDimension h e]
    (Z : X.IdealSheafData) (r : ℕ) (hZ : f.fiberClosedSubschemeDimensionLE Z r),
    FiberCycleFamily.flatPullback h hf e (closedSubschemeFiberCycleFamily f Z r hZ) =
      FiberCycleFamily.reindex (Int.natCast_add r e)
        (closedSubschemeFiberCycleFamily f' (Z.comap h) (r + e)
          (fiberClosedSubschemeDimensionLE_flatPullback h hf e Z r hZ)))

end AlgebraicGeometry.Scheme.Hom
