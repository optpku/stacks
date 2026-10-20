module

public import Mathlib.AlgebraicGeometry.Noetherian
public import Mathlib.Topology.Connected.Basic
public import ReasLib.Topology.Catenary
public import ReasLib.Topology.IrreducibleCloseds.Soberification.Basic

@[expose] public section

universe u

open Set TopologicalSpace
open scoped BigOperators

namespace AlgebraicGeometry.Scheme

variable {Y : Scheme.{u}} [IsNoetherian Y]

/-- The finite relative codimension between the irreducible closures of two comparable points
of a Noetherian scheme. -/
noncomputable def pointCodim {x y : Y} (h : x ≤ y) : ℕ :=
  ENat.toNat <|
    TopologicalSpace.codimBetween (_root_.toIrreducibleCloseds x)
      (_root_.toIrreducibleCloseds y)
      (toIrreducibleCloseds_le_iff_specializes.mpr (le_iff_specializes.mp h))

/-- Casting `pointCodim h` to `ℕ∞` recovers the relative codimension of the two point
closures. -/
theorem pointCodim_coe {x y : Y} (h : x ≤ y) :
    (pointCodim h : ℕ∞) =
      TopologicalSpace.codimBetween (_root_.toIrreducibleCloseds x)
        (_root_.toIrreducibleCloseds y)
        (toIrreducibleCloseds_le_iff_specializes.mpr (le_iff_specializes.mp h)) := sorry

namespace Distance

/-- A finite zigzag of integral point closures beginning in `Z` and ending at the point `y`. -/
structure Chain (Z : Closeds Y) (y : Y) where
  /-- The number of bridges in the zigzag. -/
  length : ℕ
  /-- The generic points of the lower irreducible closed subsets `Vᵢ`. -/
  lower : Fin (length + 1) → Y
  /-- The generic points of the upper irreducible closed subsets `Wᵢ`. -/
  upper : Fin (length + 1) → Y
  /-- Each `Vᵢ` is contained in `Wᵢ`. -/
  lower_le_upper : ∀ i, lower i ≤ upper i
  /-- Each `Vᵢ₊₁` is contained in `Wᵢ`. -/
  next_lower_le_upper : ∀ i : Fin length, lower i.succ ≤ upper i.castSucc
  /-- The first lower point lies in the prescribed closed subset. -/
  lower_zero_mem : lower 0 ∈ Z
  /-- The final upper point is the endpoint of the zigzag. -/
  upper_last_eq : upper (Fin.last length) = y

namespace Chain

/-- Construct a distance chain from its two point families, incidence relations, and endpoints. -/
def ofPoints {Z : Closeds Y} {y : Y} (length : ℕ)
    (lower upper : Fin (length + 1) → Y)
    (lower_le_upper : ∀ i, lower i ≤ upper i)
    (next_lower_le_upper : ∀ i : Fin length, lower i.succ ≤ upper i.castSucc)
    (lower_zero_mem : lower 0 ∈ Z) (upper_last_eq : upper (Fin.last length) = y) :
    Chain Z y :=
  { length := length
    lower := lower
    upper := upper
    lower_le_upper := lower_le_upper
    next_lower_le_upper := next_lower_le_upper
    lower_zero_mem := lower_zero_mem
    upper_last_eq := upper_last_eq }

/-- `ofPoints` retains the supplied chain length. -/
@[simp]
theorem ofPoints_length {Z : Closeds Y} {y : Y} (length : ℕ)
    (lower upper : Fin (length + 1) → Y)
    (lower_le_upper : ∀ i, lower i ≤ upper i)
    (next_lower_le_upper : ∀ i : Fin length, lower i.succ ≤ upper i.castSucc)
    (lower_zero_mem : lower 0 ∈ Z) (upper_last_eq : upper (Fin.last length) = y) :
    (ofPoints length lower upper lower_le_upper next_lower_le_upper
      lower_zero_mem upper_last_eq).length = length := sorry

/-- `ofPoints` retains the supplied lower point family. -/
@[simp]
theorem ofPoints_lower {Z : Closeds Y} {y : Y} (length : ℕ)
    (lower upper : Fin (length + 1) → Y)
    (lower_le_upper : ∀ i, lower i ≤ upper i)
    (next_lower_le_upper : ∀ i : Fin length, lower i.succ ≤ upper i.castSucc)
    (lower_zero_mem : lower 0 ∈ Z) (upper_last_eq : upper (Fin.last length) = y) :
    (ofPoints length lower upper lower_le_upper next_lower_le_upper
      lower_zero_mem upper_last_eq).lower = lower := sorry

/-- `ofPoints` retains the supplied upper point family. -/
@[simp]
theorem ofPoints_upper {Z : Closeds Y} {y : Y} (length : ℕ)
    (lower upper : Fin (length + 1) → Y)
    (lower_le_upper : ∀ i, lower i ≤ upper i)
    (next_lower_le_upper : ∀ i : Fin length, lower i.succ ≤ upper i.castSucc)
    (lower_zero_mem : lower 0 ∈ Z) (upper_last_eq : upper (Fin.last length) = y) :
    (ofPoints length lower upper lower_le_upper next_lower_le_upper
      lower_zero_mem upper_last_eq).upper = upper := sorry

/-- The codimension `cᵢ` of the vertical inclusion `Vᵢ ⊆ Wᵢ` in a distance chain. -/
noncomputable def verticalCodim {Z : Closeds Y} {y : Y} (C : Chain Z y)
    (i : Fin (C.length + 1)) : ℕ :=
  pointCodim (C.lower_le_upper i)

/-- The vertical codimension is the relative codimension of the corresponding point closures. -/
theorem verticalCodim_eq {Z : Closeds Y} {y : Y} (C : Chain Z y)
    (i : Fin (C.length + 1)) :
    (C.verticalCodim i : ℕ∞) =
      TopologicalSpace.codimBetween (_root_.toIrreducibleCloseds (C.lower i))
        (_root_.toIrreducibleCloseds (C.upper i))
        (toIrreducibleCloseds_le_iff_specializes.mpr
          (le_iff_specializes.mp (C.lower_le_upper i))) := sorry

/-- The codimension `bᵢ` of the bridge inclusion `Vᵢ₊₁ ⊆ Wᵢ` in a distance chain. -/
noncomputable def bridgeCodim {Z : Closeds Y} {y : Y} (C : Chain Z y)
    (i : Fin C.length) : ℕ :=
  pointCodim (C.next_lower_le_upper i)

/-- The bridge codimension is the relative codimension of the corresponding point closures. -/
theorem bridgeCodim_eq {Z : Closeds Y} {y : Y} (C : Chain Z y)
    (i : Fin C.length) :
    (C.bridgeCodim i : ℕ∞) =
      TopologicalSpace.codimBetween (_root_.toIrreducibleCloseds (C.lower i.succ))
        (_root_.toIrreducibleCloseds (C.upper i.castSucc))
        (toIrreducibleCloseds_le_iff_specializes.mpr
          (le_iff_specializes.mp (C.next_lower_le_upper i))) := sorry

/-- The cost of a distance chain: its length plus the maximum, over all starting
indices, of the vertical suffix sum minus the bridge suffix sum. -/
noncomputable def cost {Z : Closeds Y} {y : Y} (C : Chain Z y) : ℕ :=
  C.length + Finset.univ.sup (fun i : Fin (C.length + 1) ↦
    (∑ j : Fin (C.length + 1), if i ≤ j then C.verticalCodim j else 0) -
      ∑ j : Fin C.length, if i.val ≤ j.val then C.bridgeCodim j else 0)

/-- The complete finite suffix-sum formula for the cost of a distance chain. -/
theorem cost_eq {Z : Closeds Y} {y : Y} (C : Chain Z y) :
    C.cost = C.length + Finset.univ.sup (fun i : Fin (C.length + 1) ↦
      (∑ j : Fin (C.length + 1), if i ≤ j then C.verticalCodim j else 0) -
        ∑ j : Fin C.length, if i.val ≤ j.val then C.bridgeCodim j else 0) := sorry

end Chain

end Distance

/-- The distance from a point of a Noetherian scheme to a closed subset, defined as the infimum
in `ℕ∞` of the costs of all admissible finite zigzags. -/
noncomputable def distanceTo (Y : Scheme.{u}) [IsNoetherian Y] (Z : Closeds Y) : Y → ℕ∞ :=
  fun y ↦ sInf (Set.range fun C : Distance.Chain Z y ↦ (C.cost : ℕ∞))

/-- Evaluating `distanceTo` gives the infimum of the costs of all distance chains. -/
theorem distanceTo_apply (Y : Scheme.{u}) [IsNoetherian Y] (Z : Closeds Y) (y : Y) :
    Y.distanceTo Z y =
      sInf (Set.range fun C : Distance.Chain Z y ↦ (C.cost : ℕ∞)) := sorry

/-- A distance chain from `Z` to `y` exists exactly when the connected component of `y`
meets `Z`. -/
theorem distanceChain_nonempty_iff_connectedComponent_inter
    (Y : Scheme.{u}) [IsNoetherian Y] (Z : Closeds Y) (y : Y) :
    Nonempty (Distance.Chain Z y) ↔ (connectedComponent y ∩ Z).Nonempty := sorry

/-- The distance to `Z` is infinite exactly on connected components disjoint from `Z`. -/
theorem distanceTo_eq_top_iff (Y : Scheme.{u}) [IsNoetherian Y]
    (Z : Closeds Y) (y : Y) :
    Y.distanceTo Z y = ⊤ ↔ connectedComponent y ∩ Z = ∅ := sorry

/-- Whenever the connected component of `y` meets `Z`, some chain attains the distance. -/
theorem exists_chain_cost_eq_distanceTo (Y : Scheme.{u}) [IsNoetherian Y]
    (Z : Closeds Y) (y : Y) (h : (connectedComponent y ∩ Z).Nonempty) :
    ∃ C : Distance.Chain Z y, (C.cost : ℕ∞) = Y.distanceTo Z y := sorry

end AlgebraicGeometry.Scheme
