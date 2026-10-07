module

import StacksCheckRecall
public import ReasLib.AlgebraicGeometry.Scheme.FieldExtension.IrreducibleComponents

@[expose] public section

open AlgebraicGeometry

universe u

/- Lemma 33.8.10: the inverse image of an irreducible component under a
field-extension projection is a union of irreducible components of the base change. -/
@[stacks 04KW] #check
  (AlgebraicGeometry.FieldExtension.Irreducible.preimage_component_eq_iUnion :
    ∀ (k K : Type u) [Field k] [Field K] [Algebra k K]
      {X : Scheme.{u}} (f : X ⟶ Spec (CommRingCat.of k))
      (T : irreducibleComponents X),
      ∃ A : Set (irreducibleComponents (FieldExtension.baseChange k K f)),
        (FieldExtension.toSource k K f) ⁻¹' (T : Set X) =
          ⋃ Z ∈ A, (Z : Set (FieldExtension.baseChange k K f)))
