/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.AlgebraicGeometry.AlgebraicSpace.ChowGroup.RefinedGysin.RelativeCartier

/-! # Pullback along a relative effective Cartier divisor -/

@[expose] public section
open AlgebraicGeometry AlgebraicGeometry.AlgebraicSpace
open CategoryTheory
open AlgebraicGeometry.AlgebraicSpace.Hom

universe u

/- Lemma 82.24.1 Pullback -/
#check (AlgebraicGeometry.AlgebraicSpace.Hom.relativeCartierPullbackGenerator :
  ∀ {S : Scheme.{u}} {B X Y : AlgebraicSpace S}
    [UniversallyCatenary B] [IsQuasiSeparated B]
    (pY : Y ⟶ B) [QuasiSeparated pY] [LocallyOfFiniteType pY]
    (pX : X ⟶ B) [QuasiSeparated pX] [LocallyOfFiniteType pX]
    (δ : Points B → ℤ) [IsDimensionFunction δ]
    (p : X ⟶ Y) (r : ℕ) [Flat p] [RelativeDimension p r]
    (hp : p ≫ pY = pX) (D : ClosedSubspace X)
    [IsRelativeEffectiveCartierDivisor p D.ι] (n : ℤ) (y : Points Y),
    Function.locallyFinsupp
      (Points (zeroScheme D.associatedSheaf D.canonicalSection).X) ℤ)

#check (AlgebraicGeometry.AlgebraicSpace.Hom.relativeCartierPullback_locallyFiniteSupport :
  ∀ {S : Scheme.{u}} {B X Y : AlgebraicSpace S}
    [UniversallyCatenary B] [IsQuasiSeparated B]
    (pY : Y ⟶ B) [QuasiSeparated pY] [LocallyOfFiniteType pY]
    (pX : X ⟶ B) [QuasiSeparated pX] [LocallyOfFiniteType pX]
    (δ : Points B → ℤ) [IsDimensionFunction δ]
    (p : X ⟶ Y) (r : ℕ) [Flat p] [RelativeDimension p r]
    (hp : p ≫ pY = pX) (D : ClosedSubspace X)
    [IsRelativeEffectiveCartierDivisor p D.ι] (n : ℤ)
    (α : Function.locallyFinsupp (Points Y) ℤ),
    LocallyFiniteSupport fun x :
      Points (zeroScheme D.associatedSheaf D.canonicalSection).X ↦
        ∑ᶠ y : Points Y,
          α y * AlgebraicGeometry.AlgebraicSpace.Hom.relativeCartierPullbackGenerator
            pY pX δ p r hp D n y x)

#check (AlgebraicGeometry.AlgebraicSpace.Hom.relativeCartierPullbackCycle :
  ∀ {S : Scheme.{u}} {B X Y : AlgebraicSpace S}
    [UniversallyCatenary B] [IsQuasiSeparated B]
    (pY : Y ⟶ B) [QuasiSeparated pY] [LocallyOfFiniteType pY]
    (pX : X ⟶ B) [QuasiSeparated pX] [LocallyOfFiniteType pX]
    (δ : Points B → ℤ) [IsDimensionFunction δ]
    (p : X ⟶ Y) (r : ℕ) [Flat p] [RelativeDimension p r]
    (hp : p ≫ pY = pX) (D : ClosedSubspace X)
    [IsRelativeEffectiveCartierDivisor p D.ι] (n : ℤ)
    (α : Function.locallyFinsupp (Points Y) ℤ),
    Function.locallyFinsupp
      (Points (zeroScheme D.associatedSheaf D.canonicalSection).X) ℤ)

#check (AlgebraicGeometry.AlgebraicSpace.Hom.relativeCartierPullback :
  ∀ {S : Scheme.{u}} {B X Y : AlgebraicSpace S}
    [UniversallyCatenary B] [IsQuasiSeparated B]
    (pY : Y ⟶ B) [QuasiSeparated pY] [LocallyOfFiniteType pY]
    (pX : X ⟶ B) [QuasiSeparated pX] [LocallyOfFiniteType pX]
    (δ : Points B → ℤ) [IsDimensionFunction δ]
    (p : X ⟶ Y) (r : ℕ) [Flat p] [RelativeDimension p r]
    (hp : p ≫ pY = pX) (D : ClosedSubspace X)
    [IsRelativeEffectiveCartierDivisor p D.ι] (n : ℤ),
    cycleGroup pY δ n →+
      cycleGroup (zeroSchemeι D.associatedSheaf D.canonicalSection ≫ pX) δ
        (n + (r : ℤ) - 1))

#check (AlgebraicGeometry.AlgebraicSpace.Hom.chowRelativeCartierPullback :
  ∀ {S : Scheme.{u}} {B X Y : AlgebraicSpace S}
    [UniversallyCatenary B] [IsQuasiSeparated B]
    (pY : Y ⟶ B) [QuasiSeparated pY] [LocallyOfFiniteType pY]
    (pX : X ⟶ B) [QuasiSeparated pX] [LocallyOfFiniteType pX]
    (δ : Points B → ℤ) [IsDimensionFunction δ]
    (p : X ⟶ Y) (r : ℕ) [Flat p] [RelativeDimension p r]
    (hp : p ≫ pY = pX) (D : ClosedSubspace X)
    [IsRelativeEffectiveCartierDivisor p D.ι] (n : ℤ),
    chowGroup pY δ n →+
      chowGroup (zeroSchemeι D.associatedSheaf D.canonicalSection ≫ pX) δ
        (n + (r : ℤ) - 1))
