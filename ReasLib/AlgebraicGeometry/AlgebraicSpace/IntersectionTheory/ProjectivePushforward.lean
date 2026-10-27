/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.AlgebraicGeometry.AlgebraicSpace.IntersectionTheory.HigherChern
public import ReasLib.AlgebraicGeometry.AlgebraicSpace.ChowGroup.ProperPushforward

/-! Chern-power pushforward along the projectivization of a finite locally free module. -/

@[expose] public section

open CategoryTheory AlgebraicGeometry AlgebraicGeometry.AlgebraicSpace
open CategoryTheory.MonoidalCategory
open AlgebraicGeometry.AlgebraicSpace.Hom

noncomputable section

universe u

namespace AlgebraicGeometry.AlgebraicSpace.IntersectionTheory.HigherChern

variable {S : Scheme.{u}} {B X : AlgebraicSpace S}
  [UniversallyCatenary B] [IsQuasiSeparated B]
variable (f : X ⟶ B) [QuasiSeparated f] [LocallyOfFiniteType f]
variable (δ : Points B → ℤ) [IsDimensionFunction δ]
variable (E : X.Modules) (q : ℕ) [SheafOfModules.IsFiniteLocallyFreeOfRank (q + 1) E]

/-- Proper pushforward of a power of the tautological first Chern class capped
with projective-bundle pullback, sending degree `k` to degree `k + q - s`
for a module of rank `q + 1`. -/
def pushforwardC1PowerCap (k : ℤ) (s : ℕ) :
    Hom.chowGroup f δ k →+ Hom.chowGroup f δ (k + q - s) :=
  let π := ProjectiveAtlas.projection E
  let H := TautologicalDescent.O1 E
  (ChowGroup.properPushforward (π ≫ f) f δ π rfl (k + q - s)).comp
    ((FirstChernChow.power (π ≫ f) δ H s (k + q)).comp
      (ProjectiveFormulaMap.pullback f δ π q k))

/-- Evaluating the Chern-power pushforward is the composite of projective-bundle
pullback, the tautological Chern power, and proper pushforward. -/
theorem pushforwardC1PowerCap_apply (k : ℤ) (s : ℕ)
    (α : Hom.chowGroup f δ k) :
    pushforwardC1PowerCap f δ E q k s α =
      ChowGroup.properPushforward (ProjectiveAtlas.projection E ≫ f) f δ
        (ProjectiveAtlas.projection E) rfl (k + q - s)
        (FirstChernChow.power (ProjectiveAtlas.projection E ≫ f) δ
          (TautologicalDescent.O1 E) s (k + q)
          (ProjectiveFormulaMap.pullback f δ (ProjectiveAtlas.projection E) q k α)) := rfl

/-- The pushforward of the tautological Chern power capped with a pulled-back
Chow class vanishes when the power is less than the projective fibre dimension. -/
theorem pushforwardC1PowerCap_eq_zero_of_lt
    (k : ℤ) (s : ℕ) (hs : s < q) (α : Hom.chowGroup f δ k) :
    pushforwardC1PowerCap f δ E q k s α = 0 := sorry

end AlgebraicGeometry.AlgebraicSpace.IntersectionTheory.HigherChern
