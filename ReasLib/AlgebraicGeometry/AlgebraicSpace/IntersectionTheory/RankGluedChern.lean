/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module
public import ReasLib.AlgebraicGeometry.AlgebraicSpace.IntersectionTheory.HigherChern

/-! Actual Chern caps glued through the genuine Chow rank-product equivalence. -/
@[expose] public section
open CategoryTheory AlgebraicGeometry AlgebraicGeometry.AlgebraicSpace
open AlgebraicGeometry.AlgebraicSpace.Modules
noncomputable section
universe u

namespace AlgebraicGeometry.AlgebraicSpace.ChernClass

section

variable {S : Scheme.{u}} {B X : AlgebraicSpace S}
    [UniversallyCatenary B] [IsQuasiSeparated B]
    (δ : Points B → ℤ) [IsDimensionFunction δ]
    (f : X ⟶ B) [QuasiSeparated f] [LocallyOfFiniteType f]
    (E : X.Modules) [SheafOfModules.IsFiniteLocallyFree E]

/-- The Chow group is additively equivalent to the product of the Chow groups of the clopen rank loci. -/
def chowProductEquiv (k : ℤ) := AlgebraicGeometry.AlgebraicSpace.IntersectionTheory.chowProduct E f δ k

/-- The Chern cap operation on the rank-`r` locus is the constant-rank Chern operation on the restricted module. -/
def rankwiseCap (i r : ℕ) (k : ℤ) :
    Hom.chowGroup ((rankOpenSubspace E r).ι ≫ f) δ k →+
      Hom.chowGroup ((rankOpenSubspace E r).ι ≫ f) δ (k - i) :=
  AlgebraicGeometry.AlgebraicSpace.IntersectionTheory.ConstantRankChern.cap ((rankOpenSubspace E r).ι ≫ f) δ (rankModule E r) r i k

/-- The Chern cap map restricts to rank loci, applies the constant-rank Chern
operations, and glues the resulting Chow classes. -/
def gluedCap (i : ℕ) (k : ℤ) : Hom.chowGroup f δ k →+ Hom.chowGroup f δ (k - i) :=
  ((chowProductEquiv δ f E (k - i)).symm.toAddMonoidHom).comp
    ((AddMonoidHom.pi (fun r ↦ (rankwiseCap δ f E i r k).comp
      (Pi.evalAddMonoidHom (fun r ↦ Hom.chowGroup ((rankOpenSubspace E r).ι ≫ f) δ k) r))).comp
      (chowProductEquiv δ f E k).toAddMonoidHom)

/-- The Chern cap family on test spaces is obtained by gluing the constant-rank operations on their rank loci. -/
def chernClassCap (i : ℕ) : ChowCohomology.CapFamily δ f (i : ℤ) :=
  fun {Y} g _ _ k ↦ gluedCap δ (g ≫ f) ((Modules.pullback g).obj E) i k

/-- The rank-glued Chern cap family commutes with proper pushforward. -/
theorem chernClassCap_proper (i : ℕ) :
    ChowCohomology.CompatibleWithProperPushforward δ f (chernClassCap δ f E i) := by sorry
/-- The rank-glued Chern cap family commutes with flat pullback. -/
theorem chernClassCap_flat (i : ℕ) :
    ChowCohomology.CompatibleWithFlatPullback δ f (chernClassCap δ f E i) := by sorry
/-- The rank-glued Chern cap family commutes with effective Cartier divisor Gysin maps. -/
theorem chernClassCap_gysin (i : ℕ) :
    ChowCohomology.CompatibleWithCartierGysin δ f (chernClassCap δ f E i) := by sorry

/-- The Chern class of a finite locally free module is the operational class acting rankwise by constant-rank Chern caps. -/
def chernClass (i : ℕ) : ChowCohomology.degree δ f (i : ℤ) :=
  ChowCohomology.ofCap δ f (chernClassCap δ f E i)
    (chernClassCap_proper δ f E i) (chernClassCap_flat δ f E i) (chernClassCap_gysin δ f E i)

/-- The cap action of the Chern class is its rank-glued cap family. -/
theorem chernClass_cap (i : ℕ) {Y : AlgebraicSpace S} (g : Y ⟶ X)
    [QuasiSeparated (g ≫ f)] [LocallyOfFiniteType (g ≫ f)] (k : ℤ) :
    (chernClass δ f E i).cap g k = chernClassCap δ f E i g k := rfl

/-- On each pulled-back rank locus, the Chern class acts by the constant-rank Chern cap operation. -/
theorem chernClass_component {Y : AlgebraicSpace S} (g : Y ⟶ X)
    [QuasiSeparated (g ≫ f)] [LocallyOfFiniteType (g ≫ f)]
    (i r : ℕ) (k : ℤ) (a : Hom.chowGroup (g ≫ f) δ k) :
    chowProductEquiv δ (g ≫ f) ((Modules.pullback g).obj E) (k - i)
      ((chernClass δ f E i).cap g k a) r =
    rankwiseCap δ (g ≫ f) ((Modules.pullback g).obj E) i r k
      (chowProductEquiv δ (g ≫ f) ((Modules.pullback g).obj E) k a r) := by
  change ((chowProductEquiv δ (g ≫ f) ((Modules.pullback g).obj E) (k - i))
    ((chowProductEquiv δ (g ≫ f) ((Modules.pullback g).obj E) (k - i)).symm _)) r = _
  rw [AddEquiv.apply_symm_apply]
  rfl

end

/-- Chern classes of finite locally free modules on good algebraic spaces need not
vanish eventually, even with a bound allowed to depend on the module. -/
theorem chernClass_not_eventually_zero :
    ¬ ∀ {S : Scheme.{u}} {B : AlgebraicSpace S}
        [UniversallyCatenary B] [IsQuasiSeparated B]
        (δ : Points B → ℤ) [IsDimensionFunction δ]
        {X : AlgebraicSpace S} (f : X ⟶ B)
        [QuasiSeparated f] [LocallyOfFiniteType f]
        (E : X.Modules) [SheafOfModules.IsFiniteLocallyFree E],
      ∃ N : ℕ, ∀ i : ℕ, N < i →
        chernClass δ f E i = ChowCohomology.zeroCap δ f (i : ℤ) :=
  sorry

end AlgebraicGeometry.AlgebraicSpace.ChernClass
