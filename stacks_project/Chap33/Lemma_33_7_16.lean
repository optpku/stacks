module

import StacksCheckRecall
public import ReasLib.AlgebraicGeometry.Scheme.FieldExtension.ConnectedComponents

@[expose] public section

open CategoryTheory

universe u

/- Lemma 33.7.16: the source projection of a finite field-extension base change maps each
connected component to the component of its image point. -/
@[stacks 07VM] #check
  (AlgebraicGeometry.FieldExtension.Connected.image_component_eq_of_finiteDimensional :
    ∀ {k K : Type u} [Field k] [Field K] [Algebra k K] [FiniteDimensional k K]
      {X : AlgebraicGeometry.Scheme.{u}}
      (f : X ⟶ AlgebraicGeometry.Spec (CommRingCat.of k))
      (x : AlgebraicGeometry.FieldExtension.baseChange k K f),
      (AlgebraicGeometry.FieldExtension.toSource k K f).base '' connectedComponent x =
        connectedComponent
          ((AlgebraicGeometry.FieldExtension.toSource k K f).base x))
