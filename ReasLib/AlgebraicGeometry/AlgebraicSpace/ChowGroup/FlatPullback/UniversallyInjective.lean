/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.AlgebraicGeometry.AlgebraicSpace.ChowGroup.FlatPullback
public import ReasLib.AlgebraicGeometry.AlgebraicSpace.Pullback

/-! # Universal injectivity of flat pullback on Chow groups -/

@[expose] public section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry

noncomputable section

universe u

namespace AlgebraicGeometry.AlgebraicSpace.Hom

/-- A morphism has universally injective Chow pullback in relative dimension `d` if its
canonical flat pullback is injective in every degree after every good base change for
which that pullback is defined. -/
def UniversallyInjectivePullback {S : Scheme.{u}} {B X P : AlgebraicSpace S}
    [UniversallyCatenary B] [IsQuasiSeparated B]
    (pX : X ⟶ B) [QuasiSeparated pX] [LocallyOfFiniteType pX]
    (δ : Points B → ℤ) [IsDimensionFunction δ]
    (π : P ⟶ X) (d : ℕ) : Prop :=
  ∀ {Y : AlgebraicSpace S} (pY : Y ⟶ B) [QuasiSeparated pY] [LocallyOfFiniteType pY]
    (g : Y ⟶ X) (hg : g ≫ pX = pY) [Flat (pullback.fst g π)]
    [RelativeDimension (pullback.fst g π) d]
    [QuasiSeparated (pullback.fst g π ≫ pY)]
    [LocallyOfFiniteType (pullback.fst g π ≫ pY)] (k : ℤ),
    Function.Injective
      (ChowGroup.flatPullback pY (pullback.fst g π ≫ pY) δ (pullback.fst g π) d rfl k)

/-- Universal Chow-pullback injectivity specializes to a chosen good morphism over `B`
and a chosen degree. -/
theorem UniversallyInjectivePullback.injective {S : Scheme.{u}}
    {B X P : AlgebraicSpace S} [UniversallyCatenary B] [IsQuasiSeparated B]
    (pX : X ⟶ B) [QuasiSeparated pX] [LocallyOfFiniteType pX]
    (δ : Points B → ℤ) [IsDimensionFunction δ]
    (π : P ⟶ X) (d : ℕ)
    (hπ : UniversallyInjectivePullback pX δ π d)
    {Y : AlgebraicSpace S} (pY : Y ⟶ B) [QuasiSeparated pY] [LocallyOfFiniteType pY]
    (g : Y ⟶ X) (hg : g ≫ pX = pY) [Flat (pullback.fst g π)]
    [RelativeDimension (pullback.fst g π) d]
    [QuasiSeparated (pullback.fst g π ≫ pY)]
    [LocallyOfFiniteType (pullback.fst g π ≫ pY)] (k : ℤ) :
    Function.Injective
      (ChowGroup.flatPullback pY (pullback.fst g π ≫ pY) δ (pullback.fst g π) d rfl k) :=
  sorry

end AlgebraicGeometry.AlgebraicSpace.Hom
