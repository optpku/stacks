/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

import Mathlib.RingTheory.Ideal.Prod
public import ReasLib.RingTheory.Algebra.TensorProduct.Prod
public import ReasLib.RingTheory.Kaehler.NoetherDifferent

@[expose] public section

open scoped TensorProduct

universe u v w

/-- Under the canonical four-factor decomposition of `(B₁ × B₂) ⊗[A] (B₁ × B₂)`,
the annihilator of the kernel of multiplication has the component annihilators on the
diagonal factors and the zero ideals on the two cross factors. -/
theorem KaehlerDifferential.annihilator_prod (A : Type u) (B₁ : Type v) (B₂ : Type w)
    [CommRing A] [CommRing B₁] [CommRing B₂] [Algebra A B₁] [Algebra A B₂] :
    Ideal.map (Algebra.TensorProduct.prodTensorSquare A B₁ B₂).toRingEquiv.toRingHom
        (KaehlerDifferential.ideal A (B₁ × B₂)).annihilator =
      Ideal.prod
        (Ideal.prod (KaehlerDifferential.ideal A B₁).annihilator ⊥)
        (Ideal.prod ⊥ (KaehlerDifferential.ideal A B₂).annihilator) := sorry

/-- The Noether different of a product of two commutative algebras is the product
of their Noether differents. -/
theorem KaehlerDifferential.noetherDifferent_prod (A : Type u) (B₁ : Type v) (B₂ : Type w)
    [CommRing A] [CommRing B₁] [CommRing B₂] [Algebra A B₁] [Algebra A B₂] :
    KaehlerDifferential.noetherDifferent A (B₁ × B₂) =
      Ideal.prod (KaehlerDifferential.noetherDifferent A B₁)
        (KaehlerDifferential.noetherDifferent A B₂) := sorry

/-- Projection to the first factor carries the annihilator of the product
diagonal ideal to the annihilator of the first diagonal ideal. -/
theorem KaehlerDifferential.fst_mem_annihilator
    (A B₁ B₂ : Type u)
    [CommRing A] [CommRing B₁] [CommRing B₂] [Algebra A B₁] [Algebra A B₂]
    (xi : (KaehlerDifferential.ideal A (B₁ × B₂)).annihilator) :
    Algebra.TensorProduct.map (AlgHom.fst A B₁ B₂) (AlgHom.fst A B₁ B₂) xi.1 ∈
      (KaehlerDifferential.ideal A B₁).annihilator := sorry

/-- Projection to the second factor carries the annihilator of the product
diagonal ideal to the annihilator of the second diagonal ideal. -/
theorem KaehlerDifferential.snd_mem_annihilator
    (A B₁ B₂ : Type u)
    [CommRing A] [CommRing B₁] [CommRing B₂] [Algebra A B₁] [Algebra A B₂]
    (xi : (KaehlerDifferential.ideal A (B₁ × B₂)).annihilator) :
    Algebra.TensorProduct.map (AlgHom.snd A B₁ B₂) (AlgHom.snd A B₁ B₂) xi.1 ∈
      (KaehlerDifferential.ideal A B₂).annihilator := sorry
