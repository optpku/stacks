/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.AlgebraicGeometry.AlgebraicSpace.ChowGroup.RefinedGysin.RelativeCartier
import StacksCheckRecall

/-! # Gysin and first Chern class versus restriction to a relative divisor -/

@[expose] public section
open CategoryTheory AlgebraicGeometry AlgebraicGeometry.AlgebraicSpace
open AlgebraicGeometry.AlgebraicSpace.Hom
universe u

/- Lemma 82.24.1 (1) -/
@[stacks 0ERE] #check (AlgebraicGeometry.AlgebraicSpace.Hom.gysin_flatPullback_eq_relativeCartierPullback :
    ∀ {S : Scheme.{u}} {B X Y : AlgebraicSpace S}
      [UniversallyCatenary B] [IsQuasiSeparated B]
      (pY : Y ⟶ B) [QuasiSeparated pY] [LocallyOfFiniteType pY]
      (pX : X ⟶ B) [QuasiSeparated pX] [LocallyOfFiniteType pX]
      (δ : Points B → ℤ) [IsDimensionFunction δ]
      (p : X ⟶ Y) (r : ℕ) [Flat p] [RelativeDimension p r]
      (hp : p ≫ pY = pX) (D : ClosedSubspace X)
      [IsRelativeEffectiveCartierDivisor p D.ι]
      (k : ℤ) (α : Hom.cycleGroup pY δ (k + 1)),
      Hom.gysin pX δ (k + (r : ℤ)) D.associatedSheaf D.canonicalSection
          (add_right_comm k 1 (r : ℤ) ▸
            flatPullbackHom pY pX δ p r hp (k + 1) α) =
        Hom.chowMk (zeroSchemeι D.associatedSheaf D.canonicalSection ≫ pX) δ
          (k + (r : ℤ))
          (((congrArg (fun z : ℤ ↦ z - 1)
                (add_right_comm k 1 (r : ℤ))).trans
              (Int.add_sub_cancel (k + (r : ℤ)) 1)) ▸
            relativeCartierPullback pY pX δ p r hp D (k + 1) α))

/- Lemma 82.24.1 (2) -/
@[stacks 0ERE] #check (AlgebraicGeometry.AlgebraicSpace.Hom.firstChernClassCap_flatPullback_eq_pushforward_relativeCartierPullback :
    ∀ {S : Scheme.{u}} {B X Y : AlgebraicSpace S}
      [UniversallyCatenary B] [IsQuasiSeparated B]
      (pY : Y ⟶ B) [QuasiSeparated pY] [LocallyOfFiniteType pY]
      (pX : X ⟶ B) [QuasiSeparated pX] [LocallyOfFiniteType pX]
      (δ : Points B → ℤ) [IsDimensionFunction δ]
      (p : X ⟶ Y) (r : ℕ) [Flat p] [RelativeDimension p r]
      (hp : p ≫ pY = pX) (D : ClosedSubspace X)
      [IsRelativeEffectiveCartierDivisor p D.ι]
      (k : ℤ) (α : Hom.cycleGroup pY δ (k + 1)),
      firstChernClassCap pX δ D.associatedSheaf (k + (r : ℤ))
          (add_right_comm k 1 (r : ℤ) ▸
            flatPullbackHom pY pX δ p r hp (k + 1) α) =
        chowPushforward pX δ
          (zeroScheme D.associatedSheaf D.canonicalSection) (k + (r : ℤ))
          (chowMk (zeroSchemeι D.associatedSheaf D.canonicalSection ≫ pX) δ
            (k + (r : ℤ))
            (((congrArg (fun z : ℤ ↦ z - 1)
                  (add_right_comm k 1 (r : ℤ))).trans
                (Int.add_sub_cancel (k + (r : ℤ)) 1)) ▸
              relativeCartierPullback pY pX δ p r hp D (k + 1) α)))
