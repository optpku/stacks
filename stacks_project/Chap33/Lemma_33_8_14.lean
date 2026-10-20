module

public import ReasLib.AlgebraicGeometry.Scheme.FieldExtension.Galois.IrreducibleComponents
import StacksCheckRecall

@[expose] public section

open CategoryTheory AlgebraicGeometry

universe u

/- Lemma 33.8.14: fibers of the irreducible-component map after a separable closure
are exactly the orbits of the opposite Galois action. -/
@[stacks 04KY]
#check
  (AlgebraicGeometry.FieldExtension.Galois.Irreducible.componentsMap_eq_iff_exists_op :
    ∀ (k ksep : Type u) [Field k] [Field ksep] [Algebra k ksep] [IsSepClosure k ksep]
      {X : Scheme.{u}} (f : X ⟶ Spec (CommRingCat.of k))
      (T₁ T₂ : irreducibleComponents (FieldExtension.baseChange k ksep f)),
      FieldExtension.Irreducible.componentsMap k ksep f T₁ =
          FieldExtension.Irreducible.componentsMap k ksep f T₂ ↔
        ∃ σ : (Gal(ksep/k))ᵐᵒᵖ,
          AlgebraicGeometry.FieldExtension.Galois.Irreducible.opEquiv k ksep f σ T₁ = T₂)
