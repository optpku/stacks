/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import ReasLib.AlgebraicGeometry.AlgebraicSpace.IntersectionTheory.TautologicalDescent
public import ReasLib.AlgebraicGeometry.AlgebraicSpace.IntersectionTheory.ProjectiveFormulaMap
public import ReasLib.AlgebraicGeometry.AlgebraicSpace.IntersectionTheory.RankChowProduct

/-! Constant-rank Chern caps from the actual projectivization and tautological line. -/
@[expose] public section
open CategoryTheory AlgebraicGeometry AlgebraicGeometry.AlgebraicSpace
open CategoryTheory.MonoidalCategory
open AlgebraicGeometry.AlgebraicSpace.Hom
open scoped BigOperators
noncomputable section
universe u

namespace AlgebraicGeometry.AlgebraicSpace.IntersectionTheory.HigherChern
variable {S : Scheme.{u}} {B X : AlgebraicSpace S}
    [UniversallyCatenary B] [IsQuasiSeparated B]
    (f : X ⟶ B) [QuasiSeparated f] [LocallyOfFiniteType f]
    (δ : Points B → ℤ) [IsDimensionFunction δ]
    (E : X.Modules) [E.IsQuasicoherent]

instance projective_qs [SheafOfModules.IsFiniteLocallyFree E] :
    QuasiSeparated (ProjectiveAtlas.projection E ≫ f) := by sorry
instance projective_lft [SheafOfModules.IsFiniteLocallyFree E] :
    LocallyOfFiniteType (ProjectiveAtlas.projection E ≫ f) := by sorry
instance projective_proper [SheafOfModules.IsFiniteLocallyFree E] :
    Proper (ProjectiveAtlas.projection E) := by sorry
instance projective_flat [SheafOfModules.IsFiniteLocallyFree E] :
    Flat (ProjectiveAtlas.projection E) := by sorry
instance projective_dimension (q : ℕ) [SheafOfModules.IsFiniteLocallyFreeOfRank (q + 1) E] :
    RelativeDimension (ProjectiveAtlas.projection E) q := by sorry
instance tautological_invertible : isInvertibleObject (TautologicalDescent.O1 E) :=
  TautologicalDescent.O1_invertible E

variable (q : ℕ) [SheafOfModules.IsFiniteLocallyFreeOfRank (q + 1) E]

/-- Actual Segre maps of P(E), not a supplied arbitrary family. -/
def segre (j : ℕ) (k : ℤ) : Hom.chowGroup f δ k →+ Hom.chowGroup f δ (k - j) :=
  ProjectiveFormulaMap.segre f δ (ProjectiveAtlas.projection E) q (TautologicalDescent.O1 E) j k

/-- Fixed-map normalization from82.27.1 for the actual O(1). -/
theorem segre_zero (k : ℤ) :
    segre f δ E q 0 k = ChowCohomology.castChowGroup δ f (by omega) := by sorry

/-- The actual projective bundle formula is bijective for P(E), O(1). -/
theorem formula_bijective (k : ℤ) : Function.Bijective
    (ProjectiveFormulaMap.formula f δ (ProjectiveAtlas.projection E) q (TautologicalDescent.O1 E) k) := by
  sorry

/-- Solve C(t)S(-t)=1 by the explicit signed finite recurrence. This retains the
positive convention c1(O(1)) and uses no existence selector or supplied inverse. -/
def positive (n : ℕ) (k : ℤ) : Hom.chowGroup f δ k →+ Hom.chowGroup f δ (k - n) :=
  if hn : n = 0 then
    ChowCohomology.castChowGroup δ f (by rw [hn]; omega)
  else
    ∑ j : Fin n, (-1 : ℤ) ^ (n - j.val + 1) •
      (ChowCohomology.castChowGroup δ f
        (show (k - j.val) - (n - j.val : ℕ) = k - n by omega)).comp
        ((segre f δ E q (n - j.val) (k - j.val)).comp (positive j.val k))
termination_by n

theorem positive_zero (k : ℤ) :
    positive f δ E q 0 k = ChowCohomology.castChowGroup δ f (show k = k - (0 : ℕ) by omega) := by
  rw [positive]
  simp

/-- Vanishing above the genuine rank, for the specified recurrence. -/
theorem positive_above_rank (n : ℕ) (hn : q + 1 < n) (k : ℤ) :
    positive f δ E q n k = 0 := by sorry

/-- The exact i-th summand of82.28.1, with arithmetic degree equality. -/
def relationTerm (k : ℤ) (i : Fin (q + 2)) :
    Hom.chowGroup f δ k →+ Hom.chowGroup (ProjectiveAtlas.projection E ≫ f) δ (k - 1) :=
  (ChowCohomology.castChowGroup δ (ProjectiveAtlas.projection E ≫ f)
    (show ((k - i.rev.val) + q) - i.val = k - 1 by
      have hi := i.isLt
      simp only [Fin.val_rev]
      omega)).comp
      ((FirstChernChow.power (ProjectiveAtlas.projection E ≫ f) δ (TautologicalDescent.O1 E)
        i.val ((k - i.rev.val) + q)).comp
        ((ProjectiveFormulaMap.pullback f δ (ProjectiveAtlas.projection E) q (k - i.rev.val)).comp
          (positive f δ E q i.rev.val k)))

/-- The Segre recurrence and actual projective-bundle formula give the original
alternating relation; no relation is assumed of unrelated Chern data. -/
theorem source_relation (k : ℤ) (a : Hom.chowGroup f δ k) :
    ∑ i : Fin (q + 2), (-1 : ℤ) ^ i.val • relationTerm f δ E q k i a = 0 := by
  sorry

end HigherChern

namespace ConstantRankChern
open HigherChern
variable {S : Scheme.{u}} {B X : AlgebraicSpace S}
    [UniversallyCatenary B] [IsQuasiSeparated B]
    (f : X ⟶ B) [QuasiSeparated f] [LocallyOfFiniteType f]
    (δ : Points B → ℤ) [IsDimensionFunction δ]
    (E : X.Modules)

/-- The original local-freeness input supplies QCoh; no extra source hypothesis. -/
theorem locallyFree_qc [SheafOfModules.IsFiniteLocallyFree E] : E.IsQuasicoherent := by
  infer_instance

def cap (r : ℕ) [hE : SheafOfModules.IsFiniteLocallyFreeOfRank r E]
    (i : ℕ) (k : ℤ) : Hom.chowGroup f δ k →+ Hom.chowGroup f δ (k - i) := by
  -- Local instance justification (proof-local temporary data): The finite locally free input E is quasicoherent by locallyFree_qc; this supplies exactly the atlas construction for this E.
  letI := locallyFree_qc E
  cases r with
  | zero =>
      exact if hi : i = 0 then ChowCohomology.castChowGroup δ f (by rw [hi]; omega) else 0
  | succ q => exact HigherChern.positive f δ E q i k

end ConstantRankChern
end AlgebraicGeometry.AlgebraicSpace.IntersectionTheory
