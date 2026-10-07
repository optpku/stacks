module

import StacksCheckRecall
public import ReasLib.AlgebraicGeometry.Scheme.Geometrically.IrreducibleCriteria

@[expose] public section

open CategoryTheory

universe u

/- Lemma 33.8.9: a scheme over a field is geometrically irreducible if and only if every finite
separable base change is irreducible, if and only if its base change to a chosen separable
algebraic closure is irreducible. -/
@[stacks 038I]
#check (AlgebraicGeometry.GeometricallyIrreducible.Spectrum.tfae :
  ∀ {k : Type u} [Field k] {X : AlgebraicGeometry.Scheme.{u}}
    (f : X ⟶ AlgebraicGeometry.Spec (CommRingCat.of k))
    {ksep : Type u} [Field ksep] [Algebra k ksep] [IsSepClosure k ksep],
    List.TFAE
      [ AlgebraicGeometry.GeometricallyIrreducible f,
        (∀ (K : Type u) [Field K] [Algebra k K]
          [FiniteDimensional k K] [Algebra.IsSeparable k K],
          IrreducibleSpace (AlgebraicGeometry.FieldExtension.baseChange k K f)),
        IrreducibleSpace (AlgebraicGeometry.FieldExtension.baseChange k ksep f) ])

#check (AlgebraicGeometry.GeometricallyIrreducible.Spectrum.iff_finiteSeparable :
  ∀ {k : Type u} [Field k] {X : AlgebraicGeometry.Scheme.{u}}
    (f : X ⟶ AlgebraicGeometry.Spec (CommRingCat.of k)),
    AlgebraicGeometry.GeometricallyIrreducible f ↔
      ∀ (K : Type u) [Field K] [Algebra k K]
        [FiniteDimensional k K] [Algebra.IsSeparable k K],
        IrreducibleSpace (AlgebraicGeometry.FieldExtension.baseChange k K f))

#check (AlgebraicGeometry.GeometricallyIrreducible.Spectrum.iff_separableClosure :
  ∀ {k : Type u} [Field k] {X : AlgebraicGeometry.Scheme.{u}}
    (f : X ⟶ AlgebraicGeometry.Spec (CommRingCat.of k))
    {ksep : Type u} [Field ksep] [Algebra k ksep] [IsSepClosure k ksep],
    AlgebraicGeometry.GeometricallyIrreducible f ↔
      IrreducibleSpace (AlgebraicGeometry.FieldExtension.baseChange k ksep f))
