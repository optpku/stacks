module

public import Mathlib.Topology.LocallyConstant.Basic

@[expose] public section

open TopologicalSpace

universe u

namespace LocallyConstant

variable {X : Type u} [TopologicalSpace X]

/-- The clopen locus on which a locally constant natural-valued function equals `n`. -/
def fiberClopen (d : LocallyConstant X ℕ) (n : ℕ) : Clopens X :=
  ⟨{x : X | d x = n}, d.isLocallyConstant.isClopen_fiber n⟩

/-- Membership in `d.fiberClopen n` is equivalent to equality with `n`. -/
theorem mem_fiberClopen (d : LocallyConstant X ℕ) (n : ℕ) (x : X) :
    x ∈ d.fiberClopen n ↔ d x = n := sorry

end LocallyConstant
