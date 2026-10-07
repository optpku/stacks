module

public import stacks_project.Chap03.Theorem_3_8_1_Language

@[expose] public section

universe u

noncomputable section

open FirstOrder Order
open scoped ZFSet

namespace ZFSet

/-- Theorem 3.8.1. Given a finite family of formulas of set theory
`φ : Fin m → Language.setTheory.Formula (Fin n)` and a set `M0`, there exists a limit ordinal `o`
such that `M0 ⊆ V_ o` and `V_ o` reflects the conjunction of the family: for every tuple `v` from
`V_ o`, `(∀ i, (φ i).Realize ((V_ o).toSubstructure.subtype ∘ v))` if and only if
`(∀ i, (φ i).Realize v)`. -/
@[stacks 000G]
theorem exists_vonNeumann_reflects {n m : ℕ}
    (φ : Fin m → Language.setTheory.Formula (Fin n)) (M0 : ZFSet.{u}) :
    ∃ o : Ordinal.{u}, IsSuccLimit o ∧ M0 ⊆ V_ o ∧
      Reflects (V_ o) (Language.Formula.iInf φ) := sorry

end ZFSet
