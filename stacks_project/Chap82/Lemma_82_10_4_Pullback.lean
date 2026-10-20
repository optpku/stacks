/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.AlgebraicGeometry.AlgebraicSpace.CycleGroup.FlatPullback

/-! Flat pullback of cycles and its coefficient, grading, and additive interfaces. -/

open CategoryTheory AlgebraicGeometry AlgebraicGeometry.AlgebraicSpace
open Function Set Topology TopologicalSpace

universe u

namespace AlgebraicGeometry.AlgebraicSpace.ClosedSubspace

#check (AlgebraicGeometry.AlgebraicSpace.ClosedSubspace.pointClosure :
  ∀ {S : Scheme.{u}} {Y : AlgebraicSpace S} (y : Points Y),
    ClosedSubspace Y)

#check (AlgebraicGeometry.AlgebraicSpace.ClosedSubspace.pointClosure_pointsSet :
  ∀ {S : Scheme.{u}} {Y : AlgebraicSpace S}
    (y : Points Y),
    (pointClosure y).pointsSet = closure ({y} : Set (Points Y)))

end AlgebraicGeometry.AlgebraicSpace.ClosedSubspace

namespace AlgebraicGeometry.AlgebraicSpace.Hom

#check (AlgebraicGeometry.AlgebraicSpace.Hom.flatPullback_locallyFiniteSupport :
  ∀ {S : Scheme.{u}}
    {B X Y : AlgebraicSpace S} [UniversallyCatenary B] [IsQuasiSeparated B]
    (pY : Y ⟶ B) [QuasiSeparated pY] [LocallyOfFiniteType pY]
    (pX : X ⟶ B) [QuasiSeparated pX] [LocallyOfFiniteType pX]
    (δ : Points B → ℤ) [IsDimensionFunction δ]
    (f : X ⟶ Y) (r : ℕ) [Flat f] [RelativeDimension f r]
    (hf : f ≫ pY = pX) (k : ℤ) (α : Function.locallyFinsupp (Points Y) ℤ),
    LocallyFiniteSupport fun x : Points X ↦
      ∑ᶠ y : Points Y,
        α y *
          (@ClosedSubspace.associatedCycle S X
            (LocallyOfFiniteType.isLocallyNoetherian pX)
            ((ClosedSubspace.pointClosure y).inverseImageSubspace f)
            ((relativeDimensionFunction pX) δ) (k + (r : ℤ)) x))

#check (AlgebraicGeometry.AlgebraicSpace.Hom.flatPullback :
  ∀ {S : Scheme.{u}} {B X Y : AlgebraicSpace S}
    [UniversallyCatenary B] [IsQuasiSeparated B]
    (pY : Y ⟶ B) [QuasiSeparated pY] [LocallyOfFiniteType pY]
    (pX : X ⟶ B) [QuasiSeparated pX] [LocallyOfFiniteType pX]
    (δ : Points B → ℤ) [IsDimensionFunction δ]
    (f : X ⟶ Y) (r : ℕ) [Flat f] [RelativeDimension f r]
    (hf : f ≫ pY = pX) (k : ℤ) (α : Function.locallyFinsupp (Points Y) ℤ),
    Function.locallyFinsupp (Points X) ℤ)

#check (AlgebraicGeometry.AlgebraicSpace.Hom.flatPullback_apply :
  ∀ {S : Scheme.{u}} {B X Y : AlgebraicSpace S}
    [UniversallyCatenary B] [IsQuasiSeparated B]
    (pY : Y ⟶ B) [QuasiSeparated pY] [LocallyOfFiniteType pY]
    (pX : X ⟶ B) [QuasiSeparated pX] [LocallyOfFiniteType pX]
    (δ : Points B → ℤ) [IsDimensionFunction δ]
    (f : X ⟶ Y) (r : ℕ) [Flat f] [RelativeDimension f r]
    (hf : f ≫ pY = pX) (k : ℤ) (α : Function.locallyFinsupp (Points Y) ℤ)
    (x : Points X),
    flatPullback pY pX δ f r hf k α x =
      ∑ᶠ y : Points Y,
        α y *
          (@ClosedSubspace.associatedCycle S X
            (LocallyOfFiniteType.isLocallyNoetherian pX)
            ((ClosedSubspace.pointClosure y).inverseImageSubspace f)
            ((relativeDimensionFunction pX) δ) (k + (r : ℤ)) x))

#check (AlgebraicGeometry.AlgebraicSpace.Hom.flatPullback_mem_cycleGroup :
  ∀ {S : Scheme.{u}} {B X Y : AlgebraicSpace S}
    [UniversallyCatenary B] [IsQuasiSeparated B]
    (pY : Y ⟶ B) [QuasiSeparated pY] [LocallyOfFiniteType pY]
    (pX : X ⟶ B) [QuasiSeparated pX] [LocallyOfFiniteType pX]
    (δ : Points B → ℤ) [IsDimensionFunction δ]
    (f : X ⟶ Y) (r : ℕ) [Flat f] [RelativeDimension f r]
    (hf : f ≫ pY = pX) (k : ℤ) {α : Function.locallyFinsupp (Points Y) ℤ}
    (hα : α ∈ (cycleGroup pY) δ k),
    flatPullback pY pX δ f r hf k α ∈ (cycleGroup pX) δ (k + (r : ℤ)))

#check (AlgebraicGeometry.AlgebraicSpace.Hom.flatPullback_zero :
  ∀ {S : Scheme.{u}} {B X Y : AlgebraicSpace S}
    [UniversallyCatenary B] [IsQuasiSeparated B]
    (pY : Y ⟶ B) [QuasiSeparated pY] [LocallyOfFiniteType pY]
    (pX : X ⟶ B) [QuasiSeparated pX] [LocallyOfFiniteType pX]
    (δ : Points B → ℤ) [IsDimensionFunction δ]
    (f : X ⟶ Y) (r : ℕ) [Flat f] [RelativeDimension f r]
    (hf : f ≫ pY = pX) (k : ℤ),
    flatPullback pY pX δ f r hf k (0 : Function.locallyFinsupp (Points Y) ℤ) =
      0)

#check (AlgebraicGeometry.AlgebraicSpace.Hom.flatPullback_add :
  ∀ {S : Scheme.{u}} {B X Y : AlgebraicSpace S}
    [UniversallyCatenary B] [IsQuasiSeparated B]
    (pY : Y ⟶ B) [QuasiSeparated pY] [LocallyOfFiniteType pY]
    (pX : X ⟶ B) [QuasiSeparated pX] [LocallyOfFiniteType pX]
    (δ : Points B → ℤ) [IsDimensionFunction δ]
    (f : X ⟶ Y) (r : ℕ) [Flat f] [RelativeDimension f r]
    (hf : f ≫ pY = pX) (k : ℤ)
    (α β : Function.locallyFinsupp (Points Y) ℤ),
    flatPullback pY pX δ f r hf k (α + β) =
      flatPullback pY pX δ f r hf k α + flatPullback pY pX δ f r hf k β)

#check (AlgebraicGeometry.AlgebraicSpace.Hom.flatPullbackHom :
  ∀ {S : Scheme.{u}} {B X Y : AlgebraicSpace S}
    [UniversallyCatenary B] [IsQuasiSeparated B]
    (pY : Y ⟶ B) [QuasiSeparated pY] [LocallyOfFiniteType pY]
    (pX : X ⟶ B) [QuasiSeparated pX] [LocallyOfFiniteType pX]
    (δ : Points B → ℤ) [IsDimensionFunction δ]
    (f : X ⟶ Y) (r : ℕ) [Flat f] [RelativeDimension f r]
    (hf : f ≫ pY = pX) (k : ℤ),
    (cycleGroup pY) δ k →+ (cycleGroup pX) δ (k + (r : ℤ)))

#check (AlgebraicGeometry.AlgebraicSpace.Hom.flatPullback_integral :
  ∀ {S : Scheme.{u}} {B X Y : AlgebraicSpace S}
    [UniversallyCatenary B] [IsQuasiSeparated B]
    (pY : Y ⟶ B) [QuasiSeparated pY] [LocallyOfFiniteType pY]
    (pX : X ⟶ B) [QuasiSeparated pX] [LocallyOfFiniteType pX]
    (δ : Points B → ℤ) [IsDimensionFunction δ]
    (f : X ⟶ Y) (r : ℕ) [Flat f] [RelativeDimension f r]
    (hf : f ≫ pY = pX) (k : ℤ) (Z : ClosedSubspace Y) [IsIntegral Z.X]
    (hZ : (closedSubspaceDeltaDimension pY) δ Z = (k : EInt)),
    flatPullback pY pX δ f r hf k
        (@ClosedSubspace.associatedCycle S Y
          (LocallyOfFiniteType.isLocallyNoetherian pY) Z
          ((relativeDimensionFunction pY) δ) k) =
      @ClosedSubspace.associatedCycle S X
        (LocallyOfFiniteType.isLocallyNoetherian pX) (Z.inverseImageSubspace f)
        ((relativeDimensionFunction pX) δ) (k + (r : ℤ)))

end AlgebraicGeometry.AlgebraicSpace.Hom
