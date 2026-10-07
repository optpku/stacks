module

import StacksCheckRecall
public import ReasLib.RingTheory.Etale.Weakly.Field

/-!
@stack 092Q
-/

@[expose] public section

open scoped TensorProduct

universe u v

/- Lemma 15.105.16 (092Q) (1): over a field, flat tensor-square multiplication,
weakly etale, and filtered-colimit ind-etale are equivalent.  The shared owner
uses the canonical map-level and `RingHom.IndEtale` forms. -/
@[stacks 092Q "Lemma 15.105.16 (1)"]
#check fun {K B : Type u} [Field K] [CommRing B] [Algebra K B] ↦
  (Algebra.WeaklyEtale.tfae (K := K) (B := B) :
    List.TFAE
      [ (Algebra.TensorProduct.lmul' K : B ⊗[K] B →ₐ[K] B).Flat,
        Algebra.WeaklyEtale K B,
        RingHom.IndEtale.Raw (algebraMap K B) ])

/- Lemma 15.105.16 (2): every finitely generated subalgebra of a weakly
etale algebra over a field is etale. -/
@[stacks 092Q "Lemma 15.105.16 (2)"]
#check fun {K : Type u} {B : Type v} [Field K] [CommRing B] [Algebra K B]
    [Algebra.WeaklyEtale K B] (A : Subalgebra K B) (hA : A.FG) ↦
  Algebra.WeaklyEtale.etale_of_fg_subalgebra (K := K) (B := B)
    (inferInstance : Algebra.WeaklyEtale K B) A hA

#check @Algebra.WeaklyEtale.iff_tensorSquareMul_flat
#check @Algebra.WeaklyEtale.of_indEtale
#check @Algebra.WeaklyEtale.indEtale
#check @Algebra.WeaklyEtale.iff_indEtale
#check @Algebra.WeaklyEtale.etale_of_fg_subalgebra
