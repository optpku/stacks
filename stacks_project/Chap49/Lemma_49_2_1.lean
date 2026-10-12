/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import ReasLib.AlgebraicGeometry.Scheme.Morphism.OpenImmersion.FiniteSubalgebra
import StacksCheckRecall

@[expose] public section

open AlgebraicGeometry

universe u v

/- Lemma 49.2.1: two finite `A`-algebras mapping to a quasi-finite `A`-algebra, with
the induced spectrum maps open immersions, admit a common finite `A`-subalgebra of the
target through which both maps factor and whose spectrum map is an open immersion. -/
@[stacks 0BT0] #check
  (AlgebraicGeometry.IsOpenImmersion.exists_common_finiteSubalgebra :
    ∀ {A : Type u} {B B' B'' : Type v}
      [CommRing A] [CommRing B] [CommRing B'] [CommRing B'']
      [Algebra A B] [Algebra A B'] [Algebra A B'']
      (h_quasiFinite : Algebra.FiniteType.QuasiFinite A B)
      [Module.Finite A B'] [Module.Finite A B'']
      (f' : B' →ₐ[A] B) (f'' : B'' →ₐ[A] B)
      (h_open' : IsOpenImmersion (Spec.map (CommRingCat.ofHom f'.toRingHom)))
      (h_open'' : IsOpenImmersion (Spec.map (CommRingCat.ofHom f''.toRingHom))),
      ∃ C : Subalgebra A B,
        Module.Finite A C ∧
          IsOpenImmersion (Spec.map (CommRingCat.ofHom C.val.toRingHom)) ∧
            f'.range ⊔ f''.range ≤ C)
