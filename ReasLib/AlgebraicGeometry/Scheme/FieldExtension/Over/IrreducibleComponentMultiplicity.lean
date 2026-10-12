/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import Mathlib.Algebra.CharP.Defs
public import ReasLib.AlgebraicGeometry.Scheme.FieldExtension.Over.Algebraic
public import ReasLib.AlgebraicGeometry.Scheme.IrreducibleComponent.Multiplicity

@[expose] public section

open AlgebraicGeometry CategoryTheory TopologicalSpace
open scoped AlgebraicGeometry

universe u

namespace AlgebraicGeometry.SchemeOverField

/-- Field-extension base change of a locally algebraic scheme over a field is locally
Noetherian. -/
instance instIsLocallyNoetherianBaseChange
    {k : Type u} [Field k] {K : Type u} [Field K] [Algebra k K]
    {Z : SchemeOverField k} [LocallyAlgebraic Z] :
    IsLocallyNoetherian (FieldExtension.Over.baseChange k K Z).left :=
  LocallyOfFiniteType.isLocallyNoetherian (FieldExtension.Over.baseChange k K Z).hom

/-- For a field extension `K / k` and an integral locally algebraic scheme `Z` over `k`,
the multiplicity of any irreducible component of its base change to `K` is a power of the
exponential characteristic of `k`. -/
theorem irreducibleComponentMultiplicity_baseChange_eq_pow
    {k : Type u} [Field k] (K : Type u) [Field K] [Algebra k K]
    (p : ℕ) [ExpChar k p] (Z : SchemeOverField k)
    [IsIntegral Z.left] [LocallyAlgebraic Z]
    (Z' : irreducibleComponents (FieldExtension.Over.baseChange k K Z).left) :
    ∃ n : ℕ,
      (FieldExtension.Over.baseChange k K Z).left.irreducibleComponentMultiplicity Z' =
        p ^ n := sorry

/-- In characteristic zero, every irreducible component of a field-extension base change of an
integral locally algebraic scheme has multiplicity one. -/
theorem irreducibleComponentMultiplicity_baseChange_eq_one_of_charZero
    {k : Type u} [Field k] [CharZero k] (K : Type u) [Field K] [Algebra k K]
    (Z : SchemeOverField k) [IsIntegral Z.left] [LocallyAlgebraic Z]
    (Z' : irreducibleComponents (FieldExtension.Over.baseChange k K Z).left) :
    (FieldExtension.Over.baseChange k K Z).left.irreducibleComponentMultiplicity Z' = 1 := sorry

end AlgebraicGeometry.SchemeOverField
