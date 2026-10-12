/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import ReasLib.AlgebraicGeometry.Scheme.Morphism.FiniteType
public import stacks_project.Chap100.Definition_100_6_1_QuasiCompact
public import stacks_project.Chap100.Definition_100_12_3_Dimension

/-!
# Dimension of a locally Noetherian algebraic stack: value range

A nonempty algebraic stack of finite type over a field has integer dimension.
In general the dimension of a locally Noetherian algebraic stack takes values
in the extended integers, and equals `⊥` exactly on the empty stack.
-/

@[expose] public section

open CategoryTheory AlgebraicGeometry
open scoped Bicategory

universe u

namespace AlgebraicGeometry.AlgebraicStack

/-- Remark 100.12.4 (1): if `X` is a nonempty algebraic stack of finite type over a
field, then `dimension X` is an integer. -/
@[stacks 0AFQ]
theorem dimension_mem_int {k : Type u} [Field k]
    (X : GroupoidsOver (Spec (.of k))) [AlgebraicStack X]
    [IsLocallyNoetherian X] [IsQuasiCompact X] [Nonempty (Points X)]
    {U : Over (Spec (.of k))} {p : GroupoidsOver.slice U ⟶ X}
    [Groupoids.Hom.Smooth p] [Groupoids.Hom.Surjective p]
    [AlgebraicGeometry.LocallyOfFiniteType U.hom] :
    ∃ n : ℤ, dimension X = n :=
  sorry

/-- Remark 100.12.4 (2): if `X` is a locally Noetherian algebraic stack, then
`dimension X` lies in `ℤ ∪ {±∞}`. -/
@[stacks 0AFQ]
theorem dimension_trichotomy {S : Scheme.{u}} (X : GroupoidsOver S)
    [AlgebraicStack X] [IsLocallyNoetherian X] :
    dimension X = ⊥ ∨ (∃ n : ℤ, dimension X = n) ∨ dimension X = ⊤ :=
  sorry

/-- Remark 100.12.4 (3): if `X` is a locally Noetherian algebraic stack, then
`dimension X = ⊥` if and only if `X` is empty. -/
@[stacks 0AFQ]
theorem dimension_eq_bot_iff {S : Scheme.{u}} (X : GroupoidsOver S)
    [AlgebraicStack X] [IsLocallyNoetherian X] :
    dimension X = ⊥ ↔ IsEmpty (Points X) :=
  sorry

end AlgebraicGeometry.AlgebraicStack
