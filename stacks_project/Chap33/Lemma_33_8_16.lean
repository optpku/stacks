module

import StacksCheckRecall
public import ReasLib.AlgebraicGeometry.Scheme.Geometrically.FiniteSeparableComponents

@[expose] public section

open AlgebraicGeometry CategoryTheory CommRingCat

universe u

/- Lemma 33.8.16 (Tag 054R): a locally finite type scheme over a field with finitely many
irreducible components acquires geometrically irreducible canonical components after a finite
separable field extension. -/
@[stacks 054R]
#check (AlgebraicGeometry.GeometricallyIrreducible.Components.existsFiniteSeparable :
  ∀ {k : Type u} [Field k] {X : Scheme.{u}}
    (f : X ⟶ Spec (CommRingCat.of k)) [LocallyOfFiniteType f]
    [Finite (irreducibleComponents X)],
    ∃ (k' : Type u) (_ : Field k') (_ : Algebra k k')
      (_ : FiniteDimensional k k') (_ : Algebra.IsSeparable k k'),
      GeometricallyIrreducible.Components.all (FieldExtension.toBase k k' f))

end
