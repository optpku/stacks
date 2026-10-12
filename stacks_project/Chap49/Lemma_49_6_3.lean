/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

import StacksCheckRecall
public import ReasLib.RingTheory.Kaehler.NoetherDifferent.OpenImmersion

@[expose] public section

open AlgebraicGeometry

universe u v

/- Lemma 49.6.3 (1): if `A → B' → B`, the first map is of finite type, and
`Spec B → Spec B'` is an open immersion, then the annihilator of the diagonal ideal for `B`
is the extension of the corresponding annihilator for `B'`. -/
@[stacks 0BVN] #check
  (KaehlerDifferential.annihilator_eq_map_of_isOpenImmersion :
    ∀ {A : Type u} {B' B : Type v}
      [CommRing A] [CommRing B'] [CommRing B] [Algebra A B'] [Algebra A B]
      [Algebra.FiniteType A B'] (f : B' →ₐ[A] B)
      [IsOpenImmersion (Spec.map (CommRingCat.ofHom f.toRingHom))],
      (KaehlerDifferential.ideal A B).annihilator =
        Ideal.map (Algebra.TensorProduct.map f f).toRingHom
          (KaehlerDifferential.ideal A B').annihilator)

/- Lemma 49.6.3 (2): under the same hypotheses, the Noether different of `B` over `A` is
the extension of the Noether different of `B'` over `A`. -/
@[stacks 0BVN] #check
  (KaehlerDifferential.noetherDifferent_eq_map_of_isOpenImmersion :
    ∀ {A : Type u} {B' B : Type v}
      [CommRing A] [CommRing B'] [CommRing B] [Algebra A B'] [Algebra A B]
      [Algebra.FiniteType A B'] (f : B' →ₐ[A] B)
      [IsOpenImmersion (Spec.map (CommRingCat.ofHom f.toRingHom))],
      KaehlerDifferential.noetherDifferent A B =
        Ideal.map f.toRingHom (KaehlerDifferential.noetherDifferent A B'))
