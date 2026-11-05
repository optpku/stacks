module

public import Mathlib.Data.List.TFAE
public import Mathlib.AlgebraicGeometry.Geometrically.Irreducible
public import Mathlib.FieldTheory.SeparableClosure
public import Mathlib.FieldTheory.IsSepClosed
public import Mathlib.Tactic.CrossRefAttribute
public import ReasLib.AlgebraicGeometry.Scheme.FieldExtension.Basic

/-!
# Field-extension criteria for geometric irreducibility

This leaf records the finite-separable and separable-closure tests for geometric
irreducibility of a scheme morphism to the spectrum of a field.  The base-change
objects are expressed through `FieldExtension.baseChange`, so applications do not
need to reconstruct the same pullback and `Spec.map` terms.
-/

@[expose] public section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits

universe u

namespace AlgebraicGeometry

namespace GeometricallyIrreducible

section

variable {k : Type u} [Field k]
variable {X : Scheme.{u}} (f : X ⟶ Spec (CommRingCat.of k))

/-- A scheme over a field is geometrically irreducible exactly when every field-extension base
change is irreducible. -/
@[stacks 0365]
theorem iff_forall_fieldExtension :
    GeometricallyIrreducible f ↔
      ∀ (K : Type u) [Field K] [Algebra k K],
        IrreducibleSpace (FieldExtension.baseChange k K f) := sorry

namespace BaseChange

/-- Geometric irreducibility is invariant under base change along a field extension. -/
@[stacks 054P]
theorem iff_fieldExtension
    {K : Type u} [Field K] [Algebra k K] :
    GeometricallyIrreducible f ↔
      GeometricallyIrreducible (FieldExtension.toBase k K f) := sorry

/-- A scheme over a field is geometrically irreducible exactly when its self fiber product over
the field is irreducible. -/
@[stacks 0H8G]
theorem iff_selfFiberProduct :
    GeometricallyIrreducible f ↔
      IrreducibleSpace ((pullback f f : Scheme.{u})) := sorry

end BaseChange

/-- An irreducible scheme over a separably closed field is geometrically irreducible over that
field. -/
@[stacks 020J, instance]
theorem of_isSepClosed
    [IsSepClosed k] [IrreducibleSpace X] :
    GeometricallyIrreducible f := sorry

namespace BaseChange

/-- Every field-extension base change of an irreducible scheme over a separably closed field is
irreducible. -/
@[stacks 020J, instance]
theorem irreducible_of_isSepClosed
    [IsSepClosed k] [IrreducibleSpace X]
    {K : Type u} [Field K] [Algebra k K] :
    IrreducibleSpace (FieldExtension.baseChange k K f) := sorry

end BaseChange

variable {ksep : Type u} [Field ksep] [Algebra k ksep] [IsSepClosure k ksep]

namespace Spectrum

/-- Geometric irreducibility is equivalent to irreducibility after every finite
separable field extension and after one separable algebraic closure. -/
@[stacks 038I]
theorem tfae
    : List.TFAE
      [ GeometricallyIrreducible f,
        (∀ (K : Type u) [Field K] [Algebra k K]
            [FiniteDimensional k K] [Algebra.IsSeparable k K],
          IrreducibleSpace (FieldExtension.baseChange k K f)),
        IrreducibleSpace (FieldExtension.baseChange k ksep f) ] := sorry

/-- Finite separable field extensions suffice to test geometric irreducibility. -/
@[stacks 038I]
theorem iff_finiteSeparable
    : GeometricallyIrreducible f ↔
      ∀ (K : Type u) [Field K] [Algebra k K]
        [FiniteDimensional k K] [Algebra.IsSeparable k K],
        IrreducibleSpace (FieldExtension.baseChange k K f) := sorry

/-- A separable algebraic closure suffices to test geometric irreducibility. -/
@[stacks 038I]
theorem iff_separableClosure
    : GeometricallyIrreducible f ↔
      IrreducibleSpace (FieldExtension.baseChange k ksep f) := sorry

end Spectrum

end

end GeometricallyIrreducible

end AlgebraicGeometry
