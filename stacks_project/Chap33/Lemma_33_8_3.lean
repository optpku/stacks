module

import StacksCheckRecall
public import ReasLib.AlgebraicGeometry.Scheme.Geometrically.IrreducibleCriteria

@[expose] public section

open AlgebraicGeometry CommRingCat CategoryTheory Limits

universe u

/- Lemma 33.8.3 (Tag 020J): any field-valued base change of an irreducible scheme over a
separably closed field is irreducible. -/
@[stacks 020J] #check
  (AlgebraicGeometry.GeometricallyIrreducible.BaseChange.irreducible_of_isSepClosed :
    ∀ {k : Type u} [Field k] {X : Scheme.{u}}
      (f : X ⟶ Spec (CommRingCat.of k)) [IsSepClosed k] [IrreducibleSpace X]
      {K : Type u} [Field K] [Algebra k K],
      IrreducibleSpace (AlgebraicGeometry.FieldExtension.baseChange k K f))

/- Equivalently, the structure morphism is geometrically irreducible. -/
#check
  (AlgebraicGeometry.GeometricallyIrreducible.of_isSepClosed :
    ∀ {k : Type u} [Field k] {X : Scheme.{u}}
      (f : X ⟶ Spec (CommRingCat.of k)) [IsSepClosed k] [IrreducibleSpace X],
      AlgebraicGeometry.GeometricallyIrreducible f)
