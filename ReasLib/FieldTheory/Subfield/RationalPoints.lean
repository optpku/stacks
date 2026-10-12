/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import Mathlib.FieldTheory.IntermediateField.Basic
public import Mathlib.LinearAlgebra.Pi
import Mathlib.Tactic.CrossRefAttribute

/-!
# Rational points of a submodule

@stack 07P3

For a subfield `k ≤ K`, this leaf names the coordinatewise `k`-part of a submodule of a
coordinate power of `K`.  The coordinate type is arbitrary; finite-coordinate descent is
provided by the directed-intersection sibling.  No `Fin`-specific recursion or textbook proof
scaffolding belongs in this owner.
-/

@[expose] public section

universe u v

namespace Subfield

variable {K : Type u} [Field K]

/-- The coordinatewise copy of a subfield in a function space. -/
@[stacks 07P3 "coordinatewise subfield submodule"]
abbrev coordinateSubmodule (k : Subfield K) (ι : Type v) :
    Submodule k (ι → K) :=
  Submodule.pi Set.univ (fun _ : ι ↦ (⊥ : Subalgebra k K).toSubmodule)

namespace CoordinateSubmodule

/-- Membership in the coordinatewise copy is coordinatewise membership in the subfield. -/
@[simp, stacks 07P3 "coordinatewise membership"]
theorem mem_iff {k : Subfield K} {ι : Type v} {x : ι → K} :
    x ∈ k.coordinateSubmodule ι ↔ ∀ i, x i ∈ k := sorry
/- Proof strategy: unfold `coordinateSubmodule`, use `Submodule.mem_pi`, and identify the bottom
subalgebra with the canonical copy of `k` in `K`. -/

/-- Coordinatewise membership is preserved when the subfield is enlarged. -/
@[stacks 07P3 "coordinatewise inclusion"]
theorem mem_of_le {k l : Subfield K} (hkl : k ≤ l) {ι : Type v} {x : ι → K}
    (hx : x ∈ k.coordinateSubmodule ι) :
    x ∈ l.coordinateSubmodule ι := sorry
/- Proof strategy: rewrite both memberships with `CoordinateSubmodule.mem_iff` and apply `hkl`
to each coordinate. -/

end CoordinateSubmodule

end Subfield

namespace Submodule

variable {K : Type u} [Field K]

/-- The `k`-rational points of a `K`-submodule in a coordinate function space. -/
@[stacks 07P3 "rational points of a coordinate submodule"]
abbrev rationalPoints {ι : Type v} (V : Submodule K (ι → K)) (k : Subfield K) :
    Submodule k (ι → K) :=
  V.restrictScalars k ⊓ k.coordinateSubmodule ι

namespace RationalPoints

/-- Membership in rational points records submodule membership and coordinatewise field membership. -/
@[simp, stacks 07P3 "rational-point membership"]
theorem mem_iff {ι : Type v} {V : Submodule K (ι → K)} {k : Subfield K} {x : ι → K} :
    x ∈ V.rationalPoints k ↔ x ∈ V ∧ ∀ i, x i ∈ k := sorry
/- Proof strategy: unfold `rationalPoints`, use lattice intersection membership, and apply
`Subfield.CoordinateSubmodule.mem_iff`. -/

end RationalPoints

end Submodule
