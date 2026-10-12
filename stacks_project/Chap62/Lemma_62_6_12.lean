/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import Mathlib.Tactic.CrossRefAttribute
public import stacks_project.Chap62.Definition_62_6_1_Specialization

@[expose] public section

open AlgebraicGeometry CategoryTheory

noncomputable section

universe u

namespace AlgebraicGeometry.RelativeCycle

/-- The fibrewise equalizer of two families of `r`-cycles on fibres of `f : X ⟶ S`,
as the set of points `s : S` at which the fibre cycles agree. -/
def eqLocus {X S : Scheme.{u}} {f : X ⟶ S} {r : ℕ} (α β : Family f r) : Set S :=
  {s | α s = β s}

/-- A point of the base lies in the fibrewise equalizer if and only if the two
families agree on the corresponding scheme-theoretic fibre. -/
theorem mem_eqLocus {X S : Scheme.{u}} {f : X ⟶ S} {r : ℕ} {α β : Family f r}
    {s : S} : s ∈ eqLocus α β ↔ α s = β s := sorry

/-- Unfolding of the fibrewise equalizer as a set of scheme points. -/
theorem eqLocus_def {X S : Scheme.{u}} {f : X ⟶ S} {r : ℕ} (α β : Family f r) :
    eqLocus α β = {s | α s = β s} := sorry

/-- The fibrewise equalizer of `α` and `β` is the vanishing locus of `α - β`. -/
theorem eqLocus_sub {X S : Scheme.{u}} {f : X ⟶ S} {r : ℕ} (α β : Family f r) :
    eqLocus α β = eqLocus (α - β) 0 := sorry

/-- Lemma 62.6.12: if `S` is locally Noetherian and `f : X ⟶ S` is locally of finite
type, then for relative `r`-cycles `α, β` the fibrewise equalizer
`E = eqLocus α β` is a closed subset of `S`. -/
@[stacks 0H5C]
theorem isClosed_eqLocus {X S : Scheme.{u}} (f : X ⟶ S)
    [IsLocallyNoetherian S] [LocallyOfFiniteType f] {r : ℕ}
    {α β : Family f r} (hα : IsRelative α) (hβ : IsRelative β) :
    IsClosed (eqLocus α β) := sorry

/-- The fibrewise equalizer of two elements of `z(X/S, r)` is closed in `S`. -/
theorem isClosed_eqLocus_of_mem_group {X S : Scheme.{u}} (f : X ⟶ S)
    [IsLocallyNoetherian S] [LocallyOfFiniteType f] {r : ℕ}
    {α β : Family f r} (hα : α ∈ group f r) (hβ : β ∈ group f r) :
    IsClosed (eqLocus α β) := sorry

end AlgebraicGeometry.RelativeCycle
