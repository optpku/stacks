module

public import ReasLib.AlgebraicGeometry.Scheme.Geometrically.IrreducibleCriteria
import StacksCheckRecall

@[expose] public section

open CategoryTheory

universe u

/- Definition 33.8.1: a scheme over a field is geometrically irreducible exactly when its base
change along every field extension is irreducible. -/
@[stacks 0365]
#check (AlgebraicGeometry.GeometricallyIrreducible.iff_forall_fieldExtension :
  ∀ {k : Type u} [Field k] {X : AlgebraicGeometry.Scheme.{u}}
    (f : X ⟶ AlgebraicGeometry.Spec (CommRingCat.of k)),
    AlgebraicGeometry.GeometricallyIrreducible f ↔
      ∀ (K : Type u) [Field K] [Algebra k K],
        IrreducibleSpace (AlgebraicGeometry.FieldExtension.baseChange k K f))
