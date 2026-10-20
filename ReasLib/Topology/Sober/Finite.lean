module

public import Mathlib.Topology.Sober
public import Mathlib.Tactic.CrossRefAttribute

/-!
# Finite Sober Spaces

Finite topological spaces have the canonical quasi-sobriety instance needed by
finite spectral-limit constructions.
-/

@[expose] public section

universe u

variable {X : Type u} [TopologicalSpace X]

namespace Finite

/-- Every finite topological space is quasi-sober. -/
@[stacks 09XV "finite quasi-sober spaces"]
instance quasiSober [Finite X] : QuasiSober X := ⟨by
  intro S hS hSClosed
  classical
  let hSFinite : S.Finite := Set.toFinite S
  let t : Finset (Set X) := hSFinite.toFinset.image fun x ↦ closure {x}
  obtain ⟨Z, hZt, hSZ⟩ := (isIrreducible_iff_sUnion_isClosed.mp hS) t
    (by
      intro Z hZ
      obtain ⟨x, _, rfl⟩ := Finset.mem_image.mp hZ
      exact isClosed_closure)
    (by
      intro x hx
      apply Set.mem_sUnion_of_mem (subset_closure (Set.mem_singleton x))
      exact Finset.mem_coe.mpr (Finset.mem_image.mpr
        ⟨x, hSFinite.mem_toFinset.mpr hx, rfl⟩))
  obtain ⟨x, hxS, rfl⟩ := Finset.mem_image.mp hZt
  refine ⟨x, ?_⟩
  exact Set.Subset.antisymm
    (closure_minimal (Set.singleton_subset_iff.mpr (hSFinite.mem_toFinset.mp hxS)) hSClosed) hSZ⟩

end Finite
