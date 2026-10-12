/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import Mathlib.AlgebraicGeometry.Geometrically.Irreducible
public import Mathlib.FieldTheory.IsAlgClosed.AlgebraicClosure
public import Mathlib.FieldTheory.PurelyInseparable.Basic
public import Mathlib.FieldTheory.IsSepClosed
public import Mathlib.FieldTheory.SeparableClosure
public import ReasLib.AlgebraicGeometry.Scheme.FieldExtension.Basic

/-!
# Geometric irreducibility of field-extension spectra

The separably closed base-field fact is exposed as a named theorem rather
than a global instance, so geometric irreducibility remains an explicit
mathematical input where it is used.
-/

@[expose] public section

universe u

namespace AlgebraicGeometry

namespace FieldExtension.GeometricallyIrreducible

/-- The spectrum of a field extension over a separably closed field is geometrically irreducible.
-/
@[stacks 037M]
theorem of_isSepClosed
    {k K : Type u} [Field k] [IsSepClosed k] [Field K] [Algebra k K] :
    GeometricallyIrreducible (FieldExtension.specMap k K) := sorry

/-- If the relative algebraic closure of `k` in `K` is trivial, the field-extension morphism
`Spec K ⟶ Spec k` is geometrically irreducible. -/
@[stacks 037P]
theorem of_algebraicClosure_eq_bot
    {k K : Type u} [Field k] [Field K] [Algebra k K]
    (hclosed : algebraicClosure k K = ⊥) :
    GeometricallyIrreducible (FieldExtension.specMap k K) := sorry

/-- Geometric irreducibility of a field extension is equivalent to triviality of its relative
separable closure. -/
@[stacks 0G33]
theorem iff_separableClosure_eq_bot
    {k K : Type u} [Field k] [Field K] [Algebra k K] :
    GeometricallyIrreducible (FieldExtension.specMap k K) ↔
      separableClosure k K = ⊥ := sorry

/-- A field extension is geometrically irreducible exactly when every element separable over
`k` lies in the base field. -/
@[stacks 0G33]
theorem iff_forall_separable_mem_bot
    {k K : Type u} [Field k] [Field K] [Algebra k K] :
    GeometricallyIrreducible (FieldExtension.specMap k K) ↔
      ∀ α : K, IsSeparable k α → α ∈ (⊥ : IntermediateField k K) := sorry

/-- A purely inseparable field extension is geometrically irreducible. -/
@[stacks 037P "purely inseparable field extension"]
theorem of_isPurelyInseparable
    {k K : Type u} [Field k] [Field K] [Algebra k K]
    (hpi : IsPurelyInseparable k K) :
    GeometricallyIrreducible (FieldExtension.specMap k K) := sorry

/-- The relative separable closure is geometrically irreducible over the original field. -/
@[stacks 037Q]
theorem of_separableClosure
    {k K : Type u} [Field k] [Field K] [Algebra k K] :
    GeometricallyIrreducible
      (FieldExtension.specMap (separableClosure k K) K) := sorry

end FieldExtension.GeometricallyIrreducible

end AlgebraicGeometry
