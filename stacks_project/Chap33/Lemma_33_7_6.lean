module

import StacksCheckRecall
public import ReasLib.AlgebraicGeometry.Scheme.Geometrically.Connected.IsSepClosed

@[expose] public section

open AlgebraicGeometry CategoryTheory

universe u

/- Lemma 33.7.6: Let `K / k` be an extension of fields and let `X` be a scheme over `k`.
If `k` is separably algebraically closed, then the canonical morphism `X_K ⟶ X` induces a
bijection on connected components. -/
@[stacks 0363] #check
  (AlgebraicGeometry.FieldExtension.Connected.connectedComponentsMap_bijective_of_isSepClosed :
    ∀ {k K : Type u} [Field k] [IsSepClosed k] [Field K] [Algebra k K]
      {X : Scheme.{u}} (f : X ⟶ Spec (CommRingCat.of k)),
      Function.Bijective
        (((AlgebraicGeometry.FieldExtension.toSource k K f).continuous.connectedComponentsMap) :
          ConnectedComponents (AlgebraicGeometry.FieldExtension.baseChange k K f) →
            ConnectedComponents X))

/- The in-particular clause: over a separably closed field, a scheme is geometrically connected
if and only if it is connected. -/
#check
  (AlgebraicGeometry.GeometricallyConnected.iff_connectedSpace_of_isSepClosed :
    ∀ {k : Type u} [Field k] [IsSepClosed k] {X : Scheme.{u}}
      (f : X ⟶ Spec (CommRingCat.of k)),
      AlgebraicGeometry.GeometricallyConnected f ↔ ConnectedSpace X)
