module

import StacksCheckRecall
public import ReasLib.AlgebraicGeometry.Scheme.Geometrically.Normal.Normalization

@[expose] public section

universe u

/-
Lemma 33.27.4 states that every algebraic scheme over a field has a finite purely inseparable
extension over which its normalized base change is geometrically normal.
-/
@[stacks 0BXT] #check
  (AlgebraicGeometry.SchemeOverField.geometricallyNormal.exists_finitePurelyInseparableExtension_normalization :
    ∀ {k : Type u} [Field k] (X : AlgebraicGeometry.SchemeOverField k)
      [AlgebraicGeometry.Algebraic X],
      ∃ (k' : Type u) (_ : Field k') (_ : Algebra k k')
        (_ : FiniteDimensional k k') (_ : IsPurelyInseparable k k'),
        AlgebraicGeometry.SchemeOverField.geometricallyNormal
          (AlgebraicGeometry.FieldExtension.Normalization.baseChange X k'))
