/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
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
variable {S : Scheme.{u}} {B X : AlgebraicSpace S}
    [UniversallyCatenary B] [IsQuasiSeparated B]
    (δ : Points B → ℤ) [IsDimensionFunction δ]
    (f : X ⟶ B) [QuasiSeparated f] [LocallyOfFiniteType f]
    (E : X.Modules) [SheafOfModules.IsFiniteLocallyFree E]

def chowProductEquiv (k : ℤ) := AlgebraicGeometry.AlgebraicSpace.IntersectionTheory.chowProduct E f δ k

def rankwiseCap (i r : ℕ) (k : ℤ) :
    Hom.chowGroup ((rankOpenSubspace E r).ι ≫ f) δ k →+
      Hom.chowGroup ((rankOpenSubspace E r).ι ≫ f) δ (k - i) :=
  AlgebraicGeometry.AlgebraicSpace.IntersectionTheory.ConstantRankChern.cap ((rankOpenSubspace E r).ι ≫ f) δ (rankModule E r) r i k

/-- Actual restriction, factorwise canonical operation, then genuine quotient gluing. -/
def gluedCap (i : ℕ) (k : ℤ) : Hom.chowGroup f δ k →+ Hom.chowGroup f δ (k - i) :=
  ((chowProductEquiv δ f E (k - i)).symm.toAddMonoidHom).comp
    ((AddMonoidHom.pi (fun r ↦ (rankwiseCap δ f E i r k).comp
      (Pi.evalAddMonoidHom (fun r ↦ Hom.chowGroup ((rankOpenSubspace E r).ι ≫ f) δ k) r))).comp
      (chowProductEquiv δ f E k).toAddMonoidHom)

def chernClassCap (i : ℕ) : ChowCohomology.CapFamily δ f (i : ℤ) :=
  fun {Y} g _ _ k ↦ gluedCap δ (g ≫ f) ((Modules.pullback g).obj E) i k

theorem chernClassCap_proper (i : ℕ) :
    ChowCohomology.CompatibleWithProperPushforward δ f (chernClassCap δ f E i) := by sorry
theorem chernClassCap_flat (i : ℕ) :
    ChowCohomology.CompatibleWithFlatPullback δ f (chernClassCap δ f E i) := by sorry
theorem chernClassCap_gysin (i : ℕ) :
    ChowCohomology.CompatibleWithCartierGysin δ f (chernClassCap δ f E i) := by sorry

def chernClass (i : ℕ) : ChowCohomology.degree δ f (i : ℤ) :=
  ChowCohomology.ofCap δ f (chernClassCap δ f E i)
    (chernClassCap_proper δ f E i) (chernClassCap_flat δ f E i) (chernClassCap_gysin δ f E i)

theorem chernClass_cap (i : ℕ) {Y : AlgebraicSpace S} (g : Y ⟶ X)
    [QuasiSeparated (g ≫ f)] [LocallyOfFiniteType (g ≫ f)] (k : ℤ) :
    (chernClass δ f E i).cap g k = chernClassCap δ f E i g k := rfl

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

end AlgebraicGeometry.AlgebraicSpace.ChernClass
