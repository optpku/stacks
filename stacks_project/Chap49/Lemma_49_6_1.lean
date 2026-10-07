module

import StacksCheckRecall
public import ReasLib.RingTheory.Kaehler.NoetherDifferent.Prod

@[expose] public section

open scoped TensorProduct

universe u v w

/- Lemma 49.6.1 (1): under the canonical four-factor decomposition of
`(B₁ × B₂) ⊗[A] (B₁ × B₂)`, the annihilator of the kernel of multiplication is
the product of the corresponding annihilators on the diagonal factors and the
zero ideals on the two cross factors. -/
@[stacks 0BVL] #check
  (KaehlerDifferential.annihilator_prod :
    ∀ (A : Type u) (B₁ : Type v) (B₂ : Type w)
        [CommRing A] [CommRing B₁] [CommRing B₂] [Algebra A B₁] [Algebra A B₂],
      Ideal.map (Algebra.TensorProduct.prodTensorSquare A B₁ B₂).toRingEquiv.toRingHom
          (KaehlerDifferential.ideal A (B₁ × B₂)).annihilator =
        Ideal.prod
          (Ideal.prod (KaehlerDifferential.ideal A B₁).annihilator ⊥)
          (Ideal.prod ⊥ (KaehlerDifferential.ideal A B₂).annihilator))

/- Lemma 49.6.1 (2): the Noether different of `B₁ × B₂` over `A` is the
product of the Noether differents of `B₁` and `B₂` over `A`. -/
@[stacks 0BVL] #check
  (KaehlerDifferential.noetherDifferent_prod :
    ∀ (A : Type u) (B₁ : Type v) (B₂ : Type w)
        [CommRing A] [CommRing B₁] [CommRing B₂] [Algebra A B₁] [Algebra A B₂],
      KaehlerDifferential.noetherDifferent A (B₁ × B₂) =
        Ideal.prod (KaehlerDifferential.noetherDifferent A B₁)
          (KaehlerDifferential.noetherDifferent A B₂))
