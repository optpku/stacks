/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import ReasLib.AlgebraicGeometry.Scheme.Geometrically.Reduced.FiniteType
import StacksCheckRecall

@[expose] public section

universe u

/- Lemma 33.6.11: Let `k` be a field and let `X ⟶ Spec(k)` be locally of finite
type. If `X` has finitely many irreducible components, then after a suitable
finite purely inseparable extension `k' / k`, the reduction of `X` base-changed
to `k'` is geometrically reduced over `k'`. -/
@[stacks 04KT] #check
  (AlgebraicGeometry.SchemeOverField.geometricallyReduced.exists_finitePurelyInseparableExtension :
    ∀ {k : Type u} [Field k] (X : AlgebraicGeometry.SchemeOverField k)
      [AlgebraicGeometry.LocallyOfFiniteType X.hom]
      [Finite (irreducibleComponents X.left)],
      ∃ (k' : Type u) (_ : Field k') (_ : Algebra k k')
        (_ : FiniteDimensional k k') (_ : IsPurelyInseparable k k'),
        AlgebraicGeometry.SchemeOverField.geometricallyReduced
          (AlgebraicGeometry.FieldExtension.Reduced.baseChange k k' X))
