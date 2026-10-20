module

public import Mathlib.Topology.KrullDimension
public import Mathlib.Topology.Order.UpperLowerSetTopology
public import Mathlib.Tactic.CrossRefAttribute
import ReasLib.Topology.Sober.Finite

/-!
# Krull Dimension of Finite Alexandrov Chains

Dimension computations for finite linearly ordered Alexandrov spaces.
-/

@[expose] public section

open TopologicalSpace

namespace Topology.WithUpperSet

private theorem krullDim_fin_succ (n : ℕ) : Order.krullDim (Fin (n + 1)) = n := by
  rw [Order.krullDim_eq_iSup_length]
  norm_cast
  apply le_antisymm
  · refine iSup_le fun p ↦ ?_
    norm_cast
    exact Nat.le_of_lt_succ (by simpa using p.length_lt_card)
  · let p : LTSeries (Fin (n + 1)) := LTSeries.mk n id strictMono_id
    exact le_iSup_of_le p (by simp [p])

/-- The upper-set topology on the `(n + 1)`-element chain has topological Krull dimension `n`. -/
@[stacks 0057 "finite Alexandrov chains of arbitrary dimension"]
theorem topologicalKrullDim_fin_succ (n : ℕ) :
    topologicalKrullDim (Topology.WithUpperSet (Fin (n + 1))) = n := by
  letI : Fintype (Topology.WithUpperSet (Fin (n + 1))) :=
    Fintype.ofEquiv (Fin (n + 1)) Topology.WithUpperSet.toUpperSet
  letI : T0Space (Topology.WithUpperSet (Fin (n + 1))) :=
    (t0Space_iff_inseparable _).2 fun x y h ↦ by
      apply Topology.WithUpperSet.ofUpperSet.injective
      exact le_antisymm
        (Topology.WithUpperSet.ofUpperSet_le_ofUpperSet.mpr h.symm.specializes)
        (Topology.WithUpperSet.ofUpperSet_le_ofUpperSet.mpr h.specializes)
  let e₀ := irreducibleSetEquivPoints
    (α := Topology.WithUpperSet (Fin (n + 1)))
  let e : IrreducibleCloseds (Topology.WithUpperSet (Fin (n + 1))) ≃o Fin (n + 1) :=
    { toEquiv := e₀.toEquiv.trans Topology.WithUpperSet.ofUpperSet
      map_rel_iff' := by
        intro Z W
        change Topology.WithUpperSet.ofUpperSet (e₀ Z) ≤
          Topology.WithUpperSet.ofUpperSet (e₀ W) ↔ Z ≤ W
        rw [Topology.WithUpperSet.ofUpperSet_le_ofUpperSet]
        exact e₀.map_rel_iff }
  unfold topologicalKrullDim
  calc
    Order.krullDim (IrreducibleCloseds (Topology.WithUpperSet (Fin (n + 1)))) =
        Order.krullDim (Fin (n + 1)) := Order.krullDim_eq_of_orderIso e
    _ = n := krullDim_fin_succ n

end Topology.WithUpperSet
