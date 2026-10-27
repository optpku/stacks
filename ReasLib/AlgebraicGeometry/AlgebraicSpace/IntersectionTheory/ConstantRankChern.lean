/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.AlgebraicGeometry.AlgebraicSpace.IntersectionTheory.HigherChern
public import ReasLib.AlgebraicGeometry.AlgebraicSpace.IntersectionTheory.ProjectiveBaseChange
public import ReasLib.AlgebraicGeometry.AlgebraicSpace.ChowCohomology.GradedRing
public import ReasLib.AlgebraicGeometry.AlgebraicSpace.Module.FiniteLocallyFreePullback
public import Mathlib.Algebra.Group.Center

/-! # Operational Chern classes of modules of finite constant rank -/

@[expose] public section

open CategoryTheory AlgebraicGeometry AlgebraicGeometry.AlgebraicSpace
open CategoryTheory.MonoidalCategory
open AlgebraicGeometry.AlgebraicSpace.Hom
open scoped BigOperators

noncomputable section

universe u

namespace AlgebraicGeometry.AlgebraicSpace.IntersectionTheory.ConstantRankChern

open HigherChern

variable {S : Scheme.{u}} {B X : AlgebraicSpace S}
  [UniversallyCatenary B] [IsQuasiSeparated B]
variable (f : X ⟶ B) [QuasiSeparated f] [LocallyOfFiniteType f]
variable (δ : Points B → ℤ) [IsDimensionFunction δ]
variable (E : X.Modules) (q : ℕ) [SheafOfModules.IsFiniteLocallyFreeOfRank (q + 1) E]

/-- On each good test `g : Y ⟶ X`, cap with the constant-rank Chern class of `g^* E`. -/
def capFamily (i : ℕ) : OperationalChow.CapFamily δ f i :=
  fun {Y} g _ _ k ↦
    cap (g ≫ f) δ ((Modules.pullback g).obj E) (q + 1) i k

/-- Unfolding of `capFamily` as the constant-rank Chern cap of the pulled-back module. -/
theorem capFamily_apply {Y : AlgebraicSpace S} (g : Y ⟶ X)
    [QuasiSeparated (g ≫ f)] [LocallyOfFiniteType (g ≫ f)] (i : ℕ) (k : ℤ) :
    capFamily f δ E q i g k =
      cap (g ≫ f) δ ((Modules.pullback g).obj E) (q + 1) i k :=
  rfl

/-- The degree-zero constant-rank Chern cap is the identity on Chow groups. -/
theorem cap_zero {Y : AlgebraicSpace S} (g : Y ⟶ X)
    [QuasiSeparated (g ≫ f)] [LocallyOfFiniteType (g ≫ f)] (k : ℤ) :
    capFamily f δ E q 0 g k =
      (AddEquiv.cast (M := Hom.chowGroup (g ≫ f) δ) (sub_zero k).symm).toAddMonoidHom :=
  sorry

/-- The characterizing alternating relation after base change to `P(g^* E)`. -/
theorem source_relation {Y : AlgebraicSpace S} (g : Y ⟶ X)
    [QuasiSeparated (g ≫ f)] [LocallyOfFiniteType (g ≫ f)]
    (k : ℤ) (α : Hom.chowGroup (g ≫ f) δ k) :
    ∑ i : Fin (q + 2),
        (-1 : ℤ) ^ i.val •
          relationTerm (g ≫ f) δ ((Modules.pullback g).obj E) q k i α = 0 :=
  sorry

/-- The `i`-th summand of the characterizing relation on `P(g^* E)`, for a
candidate family of caps. -/
def relationTermFamily {Y : AlgebraicSpace S} (g : Y ⟶ X)
    [QuasiSeparated (g ≫ f)] [LocallyOfFiniteType (g ≫ f)]
    (c : ∀ i : Fin (q + 2), ∀ k : ℤ,
      Hom.chowGroup (g ≫ f) δ k →+ Hom.chowGroup (g ≫ f) δ (k - i.val))
    (k : ℤ) (i : Fin (q + 2)) :
    Hom.chowGroup (g ≫ f) δ k →+
      Hom.chowGroup
        (ProjectiveAtlas.projection ((Modules.pullback g).obj E) ≫ g ≫ f) δ (k - 1) :=
  (AddEquiv.cast
      (M := Hom.chowGroup
        (ProjectiveAtlas.projection ((Modules.pullback g).obj E) ≫ g ≫ f) δ)
      (show ((k - i.rev.val) + q) - i.val = k - 1 by
        have hi := i.isLt
        simp only [Fin.val_rev]
        omega)).toAddMonoidHom.comp
    ((FirstChernChow.power
        (ProjectiveAtlas.projection ((Modules.pullback g).obj E) ≫ g ≫ f) δ
        (TautologicalDescent.O1 ((Modules.pullback g).obj E)) i.val
        ((k - i.rev.val) + q)).comp
      ((ProjectiveFormulaMap.pullback (g ≫ f) δ
          (ProjectiveAtlas.projection ((Modules.pullback g).obj E)) q
          (k - i.rev.val)).comp
        (c i.rev k)))

/-- Evaluating `relationTermFamily` is the displayed composite
`c₁(𝒪_{P'}(1))^i ∩ (π')^* (c_{r-i} ∩ -)`. -/
theorem relationTermFamily_apply {Y : AlgebraicSpace S} (g : Y ⟶ X)
    [QuasiSeparated (g ≫ f)] [LocallyOfFiniteType (g ≫ f)]
    (c : ∀ i : Fin (q + 2), ∀ k : ℤ,
      Hom.chowGroup (g ≫ f) δ k →+ Hom.chowGroup (g ≫ f) δ (k - i.val))
    (k : ℤ) (i : Fin (q + 2)) (α : Hom.chowGroup (g ≫ f) δ k) :
    relationTermFamily f δ E q g c k i α =
      (AddEquiv.cast
        (M := Hom.chowGroup
          (ProjectiveAtlas.projection ((Modules.pullback g).obj E) ≫ g ≫ f) δ)
        (show ((k - i.rev.val) + q) - i.val = k - 1 by
          have hi := i.isLt
          simp only [Fin.val_rev]
          omega)).toAddMonoidHom
        (FirstChernChow.power
          (ProjectiveAtlas.projection ((Modules.pullback g).obj E) ≫ g ≫ f) δ
          (TautologicalDescent.O1 ((Modules.pullback g).obj E)) i.val
          ((k - i.rev.val) + q)
          (ProjectiveFormulaMap.pullback (g ≫ f) δ
            (ProjectiveAtlas.projection ((Modules.pullback g).obj E)) q
            (k - i.rev.val) (c i.rev k α))) :=
  rfl

/-- On a good test, any family with `c_0 = id` and the characterizing
`P(g^* E)`-relation agrees with `capFamily`. -/
theorem unique {Y : AlgebraicSpace S} (g : Y ⟶ X)
    [QuasiSeparated (g ≫ f)] [LocallyOfFiniteType (g ≫ f)]
    (c : ∀ i : Fin (q + 2), ∀ k : ℤ,
      Hom.chowGroup (g ≫ f) δ k →+ Hom.chowGroup (g ≫ f) δ (k - i.val))
    (h0 : ∀ k : ℤ, c 0 k =
      (AddEquiv.cast (M := Hom.chowGroup (g ≫ f) δ) (sub_zero k).symm).toAddMonoidHom)
    (hrel : ∀ (k : ℤ) (α : Hom.chowGroup (g ≫ f) δ k),
      ∑ i : Fin (q + 2), (-1 : ℤ) ^ i.val • relationTermFamily f δ E q g c k i α = 0)
    (i : Fin (q + 2)) (k : ℤ) :
    c i k = capFamily f δ E q i.val g k :=
  sorry

/-- Proper-pushforward compatibility of constant-rank Chern caps. -/
theorem capFamily_proper (i : ℕ) :
    OperationalChow.CompatibleWithProperPushforward δ f (capFamily f δ E q i) :=
  sorry

/-- Flat-pullback compatibility of constant-rank Chern caps. -/
theorem capFamily_flat (i : ℕ) :
    OperationalChow.CompatibleWithFlatPullback δ f (capFamily f δ E q i) :=
  sorry

/-- Cartier–Gysin compatibility of constant-rank Chern caps. -/
theorem capFamily_gysin (i : ℕ) :
    OperationalChow.CompatibleWithCartierGysin δ f (capFamily f δ E q i) :=
  sorry

/-- The degree-`i` identity bivariant class `c_i(E) ∈ A^i(X)` for
`0 ≤ i ≤ q + 1`. -/
def degree (i : ℕ) (hi : i ≤ q + 1) : OperationalChow δ f i :=
  OperationalChow.ofCap δ f (capFamily f δ E q i)
    (capFamily_proper f δ E q i) (capFamily_flat f δ E q i)
    (capFamily_gysin f δ E q i)

/-- The cap action of `degree` is `capFamily`. -/
theorem degree_cap (i : ℕ) (hi : i ≤ q + 1) {Y : AlgebraicSpace S} (g : Y ⟶ X)
    [QuasiSeparated (g ≫ f)] [LocallyOfFiniteType (g ≫ f)] (k : ℤ) :
    (degree f δ E q i hi).cap g k = capFamily f δ E q i g k :=
  rfl

/-- The total Chern class of a finite locally free `𝒪_X`-module of rank
`q + 1`, as the finite sum of its homogeneous identity classes in
`A^*(X)`. -/
def total : OperationalChow.ring δ f :=
  ∑ i : Fin (q + 2),
    OperationalChow.homogeneous δ f i.val
      (degree f δ E q i.val (Nat.lt_succ_iff.mp i.isLt))

/-- Unfolding of `total` as the sum of homogeneous embeddings of `degree`. -/
theorem total_def :
    total f δ E q =
      ∑ i : Fin (q + 2),
        OperationalChow.homogeneous δ f i.val
          (degree f δ E q i.val (Nat.lt_succ_iff.mp i.isLt)) :=
  sorry

/-- The degree-`i` component of the total Chern class is the homogeneous
class `c_i(E)`. -/
theorem total_coeff (i : ℕ) (hi : i ≤ q + 1) :
    (total f δ E q) (i : ℤ) =
      OperationalChow.Graded.ofOperational δ f (degree f δ E q i hi) :=
  sorry

end AlgebraicGeometry.AlgebraicSpace.IntersectionTheory.ConstantRankChern

namespace AlgebraicGeometry.AlgebraicSpace.IntersectionTheory.ConstantRankChern

variable {S : Scheme.{u}} {B X : AlgebraicSpace S}
  [UniversallyCatenary B] [IsQuasiSeparated B]
variable (f : X ⟶ B) [QuasiSeparated f] [LocallyOfFiniteType f]
variable (δ : Points B → ℤ) [IsDimensionFunction δ]
variable (E : X.Modules) (r : ℕ) [SheafOfModules.IsFiniteLocallyFreeOfRank r E]

/-- The degree-`i` Chern class of a finite locally free module of rank `r`,
for `i ≤ r`, with the degree-zero identity at rank zero. -/
def degreeOfRank (i : ℕ) (hi : i ≤ r) : OperationalChow δ f i := by
  cases r with
  | zero =>
      have hi0 : i = 0 := Nat.eq_zero_of_le_zero hi
      subst i
      exact OperationalChow.Graded.toOperational δ f (OperationalChow.Graded.one δ f)
  | succ q => exact degree f δ E q i hi

/-- The Chern class acts on every good test space by the constant-rank Chern
cap operation of the pulled-back module. -/
theorem degreeOfRank_cap (i : ℕ) (hi : i ≤ r) {Y : AlgebraicSpace S} (g : Y ⟶ X)
    [QuasiSeparated (g ≫ f)] [LocallyOfFiniteType (g ≫ f)] (k : ℤ) :
    (degreeOfRank f δ E r i hi).cap g k =
      cap (g ≫ f) δ ((Modules.pullback g).obj E) r i k := by
  cases r with
  | zero =>
      have hi0 : i = 0 := Nat.eq_zero_of_le_zero hi
      subst i
      rfl
  | succ q => rfl

/-- At successor rank, the Chern class is the positive-rank operational class. -/
theorem degreeOfRank_succ (q : ℕ)
    [SheafOfModules.IsFiniteLocallyFreeOfRank (q + 1) E]
    (i : ℕ) (hi : i ≤ q + 1) :
    degreeOfRank f δ E (q + 1) i hi = degree f δ E q i hi :=
  rfl

/-- The total Chern class of a finite locally free module of rank `r` is the
finite sum of its homogeneous Chern classes in degrees zero through `r`. -/
def totalOfRank : OperationalChow.ring δ f :=
  ∑ i : Fin (r + 1),
    OperationalChow.homogeneous δ f i.val
      (degreeOfRank f δ E r i.val (Nat.lt_succ_iff.mp i.isLt))

/-- The total Chern class unfolds as the sum of the homogeneous inclusions
of its Chern classes. -/
theorem totalOfRank_def :
    totalOfRank f δ E r =
      ∑ i : Fin (r + 1),
        OperationalChow.homogeneous δ f i.val
          (degreeOfRank f δ E r i.val (Nat.lt_succ_iff.mp i.isLt)) :=
  rfl

/-- At successor rank, the total Chern class is the positive-rank total. -/
theorem totalOfRank_succ (q : ℕ)
    [SheafOfModules.IsFiniteLocallyFreeOfRank (q + 1) E] :
    totalOfRank f δ E (q + 1) = total f δ E q :=
  rfl

/-- The degree-`i` component of the total Chern class is the degree-`i`
Chern class for every `i ≤ r`. -/
theorem totalOfRank_coeff (i : ℕ) (hi : i ≤ r) :
    (totalOfRank f δ E r) (i : ℤ) =
      OperationalChow.Graded.ofOperational δ f (degreeOfRank f δ E r i hi) :=
  sorry

end AlgebraicGeometry.AlgebraicSpace.IntersectionTheory.ConstantRankChern

namespace AlgebraicGeometry.AlgebraicSpace.IntersectionTheory.ConstantRankChern

variable {S : Scheme.{u}} {B X : AlgebraicSpace S}
  [UniversallyCatenary B] [IsQuasiSeparated B]
variable (δ : Points B → ℤ) [IsDimensionFunction δ]
variable (f : X ⟶ B) [QuasiSeparated f] [LocallyOfFiniteType f]
variable (E : X.Modules) (r : ℕ) [SheafOfModules.IsFiniteLocallyFreeOfRank r E]

/-- The identity class `ConstantRankChern.degreeOfRank f δ E r j hj` commutes in
`A^*(X)` with every homogeneous class `c ∈ A^p(X)`. -/
theorem comm (j : ℕ) (hj : j ≤ r) (p : ℤ) (c : OperationalChow δ f p) :
    OperationalChow.homogeneous δ f j (ConstantRankChern.degreeOfRank f δ E r j hj) * OperationalChow.homogeneous δ f p c =
      OperationalChow.homogeneous δ f p c * OperationalChow.homogeneous δ f j (ConstantRankChern.degreeOfRank f δ E r j hj) :=
  sorry

/-- Capping with `ConstantRankChern.degreeOfRank f δ E r j hj` commutes with capping
by a homogeneous identity class, after reindexing along
`k - j - p = k - p - j`. -/
theorem cap_comm (j : ℕ) (hj : j ≤ r)
    {Y : AlgebraicSpace S} (g : Y ⟶ X)
    [QuasiSeparated (g ≫ f)] [LocallyOfFiniteType (g ≫ f)]
    (p : ℤ) (c : OperationalChow δ f p) (k : ℤ) (α : Hom.chowGroup (g ≫ f) δ k) :
    (ConstantRankChern.degreeOfRank f δ E r j hj).cap g (k - p) (c.cap g k α) =
      (AddEquiv.cast (M := Hom.chowGroup (g ≫ f) δ)
        (sub_right_comm k (j : ℤ) p)).toAddMonoidHom
        (c.cap g (k - j) ((ConstantRankChern.degreeOfRank f δ E r j hj).cap g k α)) :=
  sorry

/-- The identity class `OperationalChow.homogeneous δ f j (ConstantRankChern.degreeOfRank f δ E r j hj)`
lies in the center of the Chow cohomology ring `A^*(X)`. -/
theorem mem_center (j : ℕ) (hj : j ≤ r) :
    OperationalChow.homogeneous δ f j (ConstantRankChern.degreeOfRank f δ E r j hj) ∈ Set.center (OperationalChow.ring δ f) :=
  sorry

/-- Capping with Chern identity classes of two finite locally free modules
commutes on Chow groups, after reindexing along `k - i - j = k - j - i`. -/
theorem classes_cap_comm (F : X.Modules) (s : ℕ)
    [SheafOfModules.IsFiniteLocallyFreeOfRank s F]
    {Y : AlgebraicSpace S} (g : Y ⟶ X)
    [QuasiSeparated (g ≫ f)] [LocallyOfFiniteType (g ≫ f)]
    (i : ℕ) (hi : i ≤ r) (j : ℕ) (hj : j ≤ s)
    (k : ℤ) (α : Hom.chowGroup (g ≫ f) δ k) :
    (ConstantRankChern.degreeOfRank f δ E r i hi).cap g (k - j)
        ((ConstantRankChern.degreeOfRank f δ F s j hj).cap g k α) =
      (AddEquiv.cast (M := Hom.chowGroup (g ≫ f) δ)
        (sub_right_comm k (i : ℤ) (j : ℤ))).toAddMonoidHom
        ((ConstantRankChern.degreeOfRank f δ F s j hj).cap g (k - i)
          ((ConstantRankChern.degreeOfRank f δ E r i hi).cap g k α)) :=
  sorry

end AlgebraicGeometry.AlgebraicSpace.IntersectionTheory.ConstantRankChern
