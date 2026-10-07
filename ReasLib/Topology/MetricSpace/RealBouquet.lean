module

public import Mathlib.Analysis.Normed.Lp.Finsupp
public import Mathlib.Topology.ContinuousMap.Algebra
public import Mathlib.Topology.Sets.OpenCover
import Mathlib.Tactic.CrossRefAttribute

/-!
# Bouquets of real lines

`Metric.RealBouquet ι` is the union of the coordinate axes in the `L¹` direct sum
`WithLp 1 (ι →₀ ℝ)`.  Thus all axes have one common origin, while the metric restricts to the
ordinary metric on every axis.  Metric balls at the origin give the uniform neighbourhoods across
all branches.
-/

@[expose] public section

open Filter TopologicalSpace
open scoped NNReal

noncomputable section

universe u

namespace Metric

/-- The closed exponent fact used by the canonical `L¹` metric. -/
instance instFactOneLeOneNNReal : Fact ((1 : ℝ≥0) ≤ 1) :=
  ⟨le_rfl⟩

/-- The bouquet of real lines indexed by `ι`, realized as the vectors supported on at most one
coordinate in the `L¹` direct sum. -/
@[stacks 01BL "bouquet of real lines"]
def RealBouquet (ι : Type u) :=
  {x : WithLp (1 : ℝ≥0) (ι →₀ ℝ) //
    Finset.card ((WithLp.ofLp x : ι →₀ ℝ).support) ≤ 1}

namespace RealBouquet

variable {ι : Type u}

/-- The metric inherited from the ambient `L¹` direct sum. -/
noncomputable instance instMetricSpace : MetricSpace (RealBouquet ι) :=
  Subtype.metricSpace

/-- The zero vector belongs to the union of the coordinate axes. -/
theorem origin_mem :
    Finset.card ((WithLp.ofLp (0 : WithLp (1 : ℝ≥0) (ι →₀ ℝ)) : ι →₀ ℝ).support) ≤ 1 :=
  sorry

/-- The common origin of all branches of a real bouquet. -/
@[stacks 01BL "common origin"]
noncomputable def origin : RealBouquet ι :=
  ⟨0, origin_mem⟩

/-- A vector supported on one coordinate belongs to the real bouquet. -/
theorem branch_mem (i : ι) (x : ℝ) :
    Finset.card ((WithLp.ofLp (WithLp.toLp (1 : ℝ≥0) (Finsupp.single i x)) :
      ι →₀ ℝ).support) ≤ 1 := sorry

/-- The canonical parametrization of the branch indexed by `i`. -/
@[stacks 01BL "branch parametrization"]
noncomputable def branch (i : ι) (x : ℝ) : RealBouquet ι :=
  ⟨WithLp.toLp (1 : ℝ≥0) (Finsupp.single i x), branch_mem i x⟩

/-- The `i`th coordinate of a point in a real bouquet. -/
def coordinate (i : ι) (x : RealBouquet ι) : ℝ :=
  x.1.ofLp i

/-- Every coordinate function on a real bouquet is continuous. -/
theorem continuous_coordinate (i : ι) : Continuous (coordinate i) := sorry

/-- The `i`th coordinate bundled as a continuous map. -/
noncomputable def coordinateMap (i : ι) : C(RealBouquet ι, ℝ) :=
  ⟨coordinate i, continuous_coordinate i⟩

/-- The signed coordinate on the unique branch containing a point, with value zero at the common
origin. -/
def axisValue (x : RealBouquet ι) : ℝ :=
  x.1.ofLp.sum fun _ r ↦ r

/-- The signed axis value is continuous. -/
theorem continuous_axisValue : Continuous (axisValue : RealBouquet ι → ℝ) := sorry

/-- The signed axis value bundled as a continuous map. -/
noncomputable def axisValueMap : C(RealBouquet ι, ℝ) :=
  ⟨axisValue, continuous_axisValue⟩

/-- A continuous real function transported identically to every branch. -/
noncomputable def onEachBranch (f : C(ℝ, ℝ)) : C(RealBouquet ι, ℝ) :=
  f.comp axisValueMap

/-- A continuous function supported on one branch.  Subtracting `f 0` makes it vanish on all
other branches without requiring a side condition on `f`. -/
noncomputable def supportedOn (i : ι) (f : C(ℝ, ℝ)) : C(RealBouquet ι, ℝ) :=
  f.comp (coordinateMap i) - ContinuousMap.const _ (f 0)

/-- Every branch sends zero to the common origin. -/
@[simp]
theorem branch_zero (i : ι) : branch i 0 = origin := sorry

/-- Two branch parameters determine the same bouquet point exactly when their real coordinates
agree and either that common coordinate is zero or the branch indices agree. -/
@[stacks 01BL "branch identification"]
theorem branch_eq_branch_iff (i j : ι) (x y : ℝ) :
    branch i x = branch j y ↔ x = y ∧ (x = 0 ∨ i = j) := sorry

/-- A coordinate evaluates to the branch parameter on its own branch. -/
@[simp]
theorem coordinate_branch_same (i : ι) (x : ℝ) :
    coordinate i (branch i x) = x := sorry

/-- A coordinate vanishes on every different branch. -/
theorem coordinate_branch_ne {i j : ι} (h : i ≠ j) (x : ℝ) :
    coordinate i (branch j x) = 0 := sorry

/-- The signed axis value restricts to the identity on every branch. -/
@[simp]
theorem axisValue_branch (i : ι) (x : ℝ) : axisValue (branch i x) = x := sorry

/-- A branch-supported function has the expected value on its supporting branch. -/
theorem supportedOn_branch_same (i : ι) (f : C(ℝ, ℝ)) (x : ℝ) :
    supportedOn i f (branch i x) = f x - f 0 := sorry

/-- When `f` vanishes at zero, its branch-supported extension agrees with `f` on the supporting
branch without a normalization term. -/
@[stacks 01BL "normalized branch-supported function"]
theorem supportedOn_branch_same_of_zero (i : ι) (f : C(ℝ, ℝ))
    (hf : f 0 = 0) (x : ℝ) :
    supportedOn i f (branch i x) = f x := sorry

/-- A branch-supported function vanishes on every different branch. -/
theorem supportedOn_branch_ne {i j : ι} (h : i ≠ j) (f : C(ℝ, ℝ)) (x : ℝ) :
    supportedOn i f (branch j x) = 0 := sorry

/-- The uniform open ball of radius `r` about the common origin. -/
def uniformBall (r : ℝ) : Opens (RealBouquet ι) :=
  ⟨Metric.ball origin r, Metric.isOpen_ball⟩

/-- The standard uniform neighbourhood with radius `(n + 1)⁻¹`. -/
@[stacks 01BL "uniform neighbourhood"]
def standardNeighborhood (n : ℕ) : Opens (RealBouquet ι) :=
  uniformBall (((n + 1 : ℕ) : ℝ)⁻¹)

/-- The standard uniform neighbourhoods form a neighbourhood basis at the common origin. -/
@[stacks 01BL "uniform neighbourhood basis"]
theorem nhds_origin_hasBasis :
    (nhds (origin : RealBouquet ι)).HasBasis (fun _ : ℕ ↦ True)
      (fun n ↦ (standardNeighborhood (ι := ι) n : Set (RealBouquet ι))) := sorry

/-- When there are infinitely many branches, no set belonging to the neighbourhood filter of the
common origin is compact. -/
@[stacks 01BL "origin has no compact neighbourhood"]
theorem not_isCompact_of_mem_nhds_origin [Infinite ι] {K : Set (RealBouquet ι)}
    (hK : K ∈ nhds origin) : ¬ IsCompact K := sorry

/-- A real bouquet with infinitely many branches admits no locally compact space structure
compatible with its canonical metric topology. -/
@[stacks 01BL "not locally compact"]
theorem not_locallyCompactSpace [Infinite ι] :
    ¬ LocallyCompactSpace (RealBouquet ι) := sorry

/-- Membership in a standard neighbourhood is the same interval condition on every branch. -/
theorem branch_mem_standardNeighborhood_iff (i : ι) (x : ℝ) (n : ℕ) :
    branch i x ∈ standardNeighborhood n ↔ |x| < (((n + 1 : ℕ) : ℝ)⁻¹) := sorry

/-- The punctured part of one branch, described by its nonzero coordinate. -/
def branchAway (i : ι) : Set (RealBouquet ι) :=
  {x | coordinate i x ≠ 0}

/-- The punctured part of a branch is open. -/
theorem isOpen_branchAway (i : ι) : IsOpen (branchAway i) := sorry

/-- The punctured part of one branch as an open subspace. -/
def branchOpen (i : ι) : Opens (RealBouquet ι) :=
  ⟨branchAway i, isOpen_branchAway i⟩

/-- The cover consisting of one uniform neighbourhood and all punctured branches. -/
def standardCover (n : ℕ) : Option ι → Opens (RealBouquet ι)
  | none => standardNeighborhood n
  | some i => branchOpen i

/-- A uniform neighbourhood together with all punctured branches covers the real bouquet. -/
theorem standardCover_isOpenCover (n : ℕ) : IsOpenCover (standardCover (ι := ι) n) := sorry

end RealBouquet

end Metric
