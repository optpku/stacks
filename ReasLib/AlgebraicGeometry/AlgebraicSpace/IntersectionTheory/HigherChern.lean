/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
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

/-- The projective bundle of a finite locally free module is quasi-separated over the base. -/
instance projective_qs [SheafOfModules.IsFiniteLocallyFree E] :
    QuasiSeparated (ProjectiveAtlas.projection E ≫ f) := by sorry
/-- The projective bundle of a finite locally free module is locally of finite type over the base. -/
instance projective_lft [SheafOfModules.IsFiniteLocallyFree E] :
    LocallyOfFiniteType (ProjectiveAtlas.projection E ≫ f) := by sorry
/-- The projection of a finite locally free projective bundle is proper. -/
instance projective_proper [SheafOfModules.IsFiniteLocallyFree E] :
    Proper (ProjectiveAtlas.projection E) := by sorry
/-- The projection of a finite locally free projective bundle is flat. -/
instance projective_flat [SheafOfModules.IsFiniteLocallyFree E] :
    Flat (ProjectiveAtlas.projection E) := by sorry
/-- The projective bundle of a module of rank `q + 1` has relative dimension `q`. -/
instance projective_dimension (q : ℕ) [SheafOfModules.IsFiniteLocallyFreeOfRank (q + 1) E] :
    RelativeDimension (ProjectiveAtlas.projection E) q := by sorry
/-- The tautological quotient module on a projective bundle is invertible. -/
instance tautological_invertible : isInvertibleObject (TautologicalDescent.O1 E) :=
  TautologicalDescent.O1_invertible E

/-- The component of the projective-bundle formula is flat pullback followed by
the indicated power of the tautological first Chern class, transported to degree `k + r - 1`. -/
def formulaTerm (r : ℕ) [SheafOfModules.IsFiniteLocallyFreeOfRank r E]
    (k : ℤ) (i : Fin r) :
    Hom.chowGroup f δ (k + i.val) →+
      Hom.chowGroup (ProjectiveAtlas.projection E ≫ f) δ (k + (r : ℤ) - 1) := by
  cases r with
  | zero => exact Fin.elim0 i
  | succ q =>
      exact (ChowCohomology.castChowGroup δ (ProjectiveAtlas.projection E ≫ f)
        (show k + (q : ℤ) = k + ((q + 1 : ℕ) : ℤ) - 1 by omega)).comp
          (ProjectiveFormulaMap.term f δ (ProjectiveAtlas.projection E) q
            (TautologicalDescent.O1 E) k i)

/-- At successor rank, a formula component is the usual positive-rank component
followed by the arithmetic transport of the target degree. -/
theorem formulaTerm_succ (q : ℕ) [SheafOfModules.IsFiniteLocallyFreeOfRank (q + 1) E]
    (k : ℤ) (i : Fin (q + 1)) :
    formulaTerm f δ E (q + 1) k i =
      (ChowCohomology.castChowGroup δ (ProjectiveAtlas.projection E ≫ f)
        (show k + (q : ℤ) = k + ((q + 1 : ℕ) : ℤ) - 1 by omega)).comp
          (ProjectiveFormulaMap.term f δ (ProjectiveAtlas.projection E) q
            (TautologicalDescent.O1 E) k i) := rfl

/-- At successor rank, evaluating a formula component gives the transported
pullback and tautological Chern-power cap. -/
theorem formulaTerm_apply (q : ℕ) [SheafOfModules.IsFiniteLocallyFreeOfRank (q + 1) E]
    (k : ℤ) (i : Fin (q + 1)) (a : Hom.chowGroup f δ (k + i.val)) :
    formulaTerm f δ E (q + 1) k i a =
      ChowCohomology.castChowGroup δ (ProjectiveAtlas.projection E ≫ f)
        (show k + (q : ℤ) = k + ((q + 1 : ℕ) : ℤ) - 1 by omega)
        (ProjectiveFormulaMap.term f δ (ProjectiveAtlas.projection E) q
          (TautologicalDescent.O1 E) k i a) := rfl

/-- The projective-bundle formula map sums flat pullbacks capped with powers of
the tautological first Chern class; at rank zero this is the empty sum. -/
def formulaMap (r : ℕ) [SheafOfModules.IsFiniteLocallyFreeOfRank r E] (k : ℤ) :
    (∀ i : Fin r, Hom.chowGroup f δ (k + i.val)) →+
      Hom.chowGroup (ProjectiveAtlas.projection E ≫ f) δ (k + (r : ℤ) - 1) :=
  ∑ i : Fin r, (formulaTerm f δ E r k i).comp
    (Pi.evalAddMonoidHom (fun j : Fin r ↦ Hom.chowGroup f δ (k + j.val)) i)

/-- The projective-bundle formula map evaluates as the sum of its components. -/
theorem formulaMap_apply (r : ℕ) [SheafOfModules.IsFiniteLocallyFreeOfRank r E]
    (k : ℤ) (a : ∀ i : Fin r, Hom.chowGroup f δ (k + i.val)) :
    formulaMap f δ E r k a = ∑ i : Fin r, formulaTerm f δ E r k i (a i) := by
  simp [formulaMap]

/-- The projective-bundle formula map is bijective in every degree and at every finite rank. -/
theorem formulaMap_bijective (r : ℕ) [SheafOfModules.IsFiniteLocallyFreeOfRank r E]
    (k : ℤ) : Function.Bijective (formulaMap f δ E r k) := by
  sorry

variable (q : ℕ) [SheafOfModules.IsFiniteLocallyFreeOfRank (q + 1) E]

/-- The Segre operation is flat pullback, tautological Chern-power cap, and proper pushforward. -/
def segre (j : ℕ) (k : ℤ) : Hom.chowGroup f δ k →+ Hom.chowGroup f δ (k - j) :=
  ProjectiveFormulaMap.segre f δ (ProjectiveAtlas.projection E) q (TautologicalDescent.O1 E) j k

/-- The degree-zero Segre operation is the identity up to degree transport. -/
theorem segre_zero (k : ℤ) :
    segre f δ E q 0 k = ChowCohomology.castChowGroup δ f (by omega) := by sorry

/-- The positive-rank projective-bundle formula is bijective in every Chow degree. -/
theorem formula_bijective (k : ℤ) : Function.Bijective
    (ProjectiveFormulaMap.formula f δ (ProjectiveAtlas.projection E) q (TautologicalDescent.O1 E) k) := by
  sorry

/-- The Chern operations are defined by the signed finite recurrence `C(t)S(-t) = 1`
for the Segre operations with the positive tautological first Chern class convention. -/
def positive (n : ℕ) (k : ℤ) : Hom.chowGroup f δ k →+ Hom.chowGroup f δ (k - n) :=
  if hn : n = 0 then
    ChowCohomology.castChowGroup δ f (by rw [hn]; omega)
  else
    ∑ j : Fin n, (-1 : ℤ) ^ (n - j.val + 1) •
      (ChowCohomology.castChowGroup δ f
        (show (k - j.val) - (n - j.val : ℕ) = k - n by omega)).comp
        ((segre f δ E q (n - j.val) (k - j.val)).comp (positive j.val k))
termination_by n

/-- The degree-zero Chern operation is the identity up to degree transport. -/
theorem positive_zero (k : ℤ) :
    positive f δ E q 0 k = ChowCohomology.castChowGroup δ f (show k = k - (0 : ℕ) by omega) := by
  rw [positive]
  simp

/-- Chern operations vanish in degrees above the rank of the module. -/
theorem positive_above_rank (n : ℕ) (hn : q + 1 < n) (k : ℤ) :
    positive f δ E q n k = 0 := by sorry

/-- A projective-bundle relation term is the complementary Chern operation,
followed by flat pullback and a tautological Chern-power cap, in degree `k - 1`. -/
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

/-- The alternating sum of the Chern and tautological Chern-power terms vanishes
on the projective bundle. -/
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

/-- A finite locally free module is quasicoherent. -/
theorem locallyFree_qc [SheafOfModules.IsFiniteLocallyFree E] : E.IsQuasicoherent := by
  infer_instance

/-- The Chern cap operation of a constant-rank module is given by the Segre
recurrence at positive rank, and by the identity in degree zero at rank zero. -/
def cap (r : ℕ) [hE : SheafOfModules.IsFiniteLocallyFreeOfRank r E]
    (i : ℕ) (k : ℤ) : Hom.chowGroup f δ k →+ Hom.chowGroup f δ (k - i) := by
  cases r with
  | zero =>
      exact if hi : i = 0 then ChowCohomology.castChowGroup δ f (by rw [hi]; omega) else 0
  | succ q => exact HigherChern.positive f δ E q i k

end ConstantRankChern
end AlgebraicGeometry.AlgebraicSpace.IntersectionTheory
