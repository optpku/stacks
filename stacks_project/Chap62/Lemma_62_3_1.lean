module

import StacksCheckRecall
public import ReasLib.AlgebraicGeometry.Scheme.FieldExtension.Over.IrreducibleComponentMultiplicity

@[expose] public section

open AlgebraicGeometry CategoryTheory TopologicalSpace
open scoped AlgebraicGeometry

universe u

/- Lemma 62.3.1: for a field extension `K / k` and an integral locally algebraic scheme `Z`
over `k`, the multiplicity of any irreducible component of its base change to `K` is a power
of the exponential characteristic of `k`. -/
@[stacks 0H4F] #check
  (AlgebraicGeometry.SchemeOverField.irreducibleComponentMultiplicity_baseChange_eq_pow :
    ∀ {k : Type u} [Field k] (K : Type u) [Field K] [Algebra k K]
      (p : ℕ) [ExpChar k p] (Z : SchemeOverField k)
      [IsIntegral Z.left] [LocallyAlgebraic Z]
      (Z' : irreducibleComponents (FieldExtension.Over.baseChange k K Z).left),
    ∃ n : ℕ,
      (FieldExtension.Over.baseChange k K Z).left.irreducibleComponentMultiplicity Z' =
        p ^ n)

/- In characteristic zero, every irreducible component of a field-extension base change of an
integral locally algebraic scheme has multiplicity one. -/
#check
  (AlgebraicGeometry.SchemeOverField.irreducibleComponentMultiplicity_baseChange_eq_one_of_charZero :
    ∀ {k : Type u} [Field k] [CharZero k] (K : Type u) [Field K] [Algebra k K]
      (Z : SchemeOverField k) [IsIntegral Z.left] [LocallyAlgebraic Z]
      (Z' : irreducibleComponents (FieldExtension.Over.baseChange k K Z).left),
    (FieldExtension.Over.baseChange k K Z).left.irreducibleComponentMultiplicity Z' = 1)
