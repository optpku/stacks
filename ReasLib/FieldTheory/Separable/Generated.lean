module

public import Mathlib.FieldTheory.SeparablyGenerated
public import Mathlib.RingTheory.AlgebraicIndependent.Defs
public import Mathlib.Tactic.CrossRefAttribute

@[expose] public section

/-!
# Separably Generated Field Extensions

A field extension is separably generated if it admits a transcendence basis over which the
remaining extension is separable algebraic. It is separable over the base if all finitely
generated intermediate subextensions are separably generated.

## Main definitions

* `Algebra.IsSeparablyGenerated` — admits a separating transcendence basis.
* `Algebra.IsSeparableOver` — all finitely generated intermediate fields are separably generated.
-/

universe u v

open scoped IntermediateField

section

variable (k : Type u) (K : Type v) [Field k] [Field K] [Algebra k K]

namespace Algebra

/-- A field extension `K / k` is separably generated if there exists a
transcendence basis `s ⊆ K` over `k` such that `K / k(s)` is separable algebraic. -/
@[stacks 030O "(1)"]
class IsSeparablyGenerated : Prop where
  /-- A separating transcendence basis exists. -/
  existsSeparatingBasis :
    ∃ s : Set K, IsTranscendenceBasis k (Subtype.val : s → K) ∧
      Algebra.IsSeparable (IntermediateField.adjoin k s) K

/-- `Algebra.IsSeparablyGenerated k K` is exactly the existence of a separating transcendence
basis for `K / k`. -/
@[stacks 030O "separably generated characterization"]
theorem isSeparablyGenerated_iff :
    IsSeparablyGenerated k K ↔
      ∃ s : Set K, IsTranscendenceBasis k (Subtype.val : s → K) ∧
        Algebra.IsSeparable (IntermediateField.adjoin k s) K := by
  constructor
  · rintro ⟨h⟩
    exact h
  · exact fun h ↦ ⟨h⟩

/-- A field extension `K / k` is separable over `k` when every finitely
generated intermediate extension is separably generated. -/
@[stacks 030O "(2)"]
class IsSeparableOver : Prop where
  /-- Every finitely generated intermediate field is separably generated over the base. -/
  isSeparablyGenerated_of_fg :
    ∀ L : IntermediateField k K, L.FG → Algebra.IsSeparablyGenerated k L

/-- `Algebra.IsSeparableOver k K` is exactly separable generatedness of every finitely generated
intermediate field of `K / k`. -/
@[stacks 030O "separable-over characterization"]
theorem isSeparableOver_iff :
    IsSeparableOver k K ↔
      ∀ L : IntermediateField k K, L.FG → Algebra.IsSeparablyGenerated k L := by
  constructor
  · rintro ⟨h⟩
    exact h
  · exact fun h ↦ ⟨h⟩

end Algebra

end
