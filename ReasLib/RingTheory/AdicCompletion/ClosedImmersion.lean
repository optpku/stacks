module

public import Mathlib.RingTheory.FiniteType
public import Mathlib.RingTheory.Noetherian.Defs
public import Mathlib.RingTheory.TensorProduct.Quotient
public import ReasLib.RingTheory.AdicCompletion.RingEquiv

/-!
# Closed-immersion base change of adic completions

This file identifies the completion of a quotient-base tensor product with
the corresponding quotient of the complete algebra.
-/

@[expose] public section

noncomputable section

universe u

open TensorProduct

open scoped TensorProduct

namespace IsAdicComplete

/-- If `B` is complete over a Noetherian pair `(A, I)` and `Ibar` is cofinal
with the image of `I` in `A ⧸ a`, then `B ⧸ aB` is `Ibar`-adically complete. -/
theorem quotIdealMap {A B : Type u} [CommRing A] [IsNoetherianRing A] [CommRing B]
    [Algebra A B] (I a : Ideal A) [IsAdicComplete I B]
    [Algebra.FiniteType (A ⧸ I) (B ⧸ I.map (algebraMap A B))]
    (Ibar : Ideal (A ⧸ a)) {c d : ℕ} (hc : 0 < c) (hd : 0 < d)
    (hI : I.map (Ideal.Quotient.mk a) ^ c ≤ Ibar)
    (hIbar : Ibar ^ d ≤ I.map (Ideal.Quotient.mk a)) :
    IsAdicComplete (Ibar.map (algebraMap (A ⧸ a) (B ⧸ a.map (algebraMap A B))))
      (B ⧸ a.map (algebraMap A B)) := sorry

end IsAdicComplete

namespace AdicCompletion

variable {A B : Type u} [CommRing A] [CommRing B] [Algebra A B]

/-- The extension of `Ibar` to `B ⊗[A] (A ⧸ a)` along `includeRight`. -/
def tensorIncludeRightIdeal (B : Type u) [CommRing B] [Algebra A B]
    (a : Ideal A) (Ibar : Ideal (A ⧸ a)) :
    Ideal (B ⊗[A] (A ⧸ a)) :=
  Ibar.map (Algebra.TensorProduct.includeRight :
    (A ⧸ a) →ₐ[A] B ⊗[A] (A ⧸ a)).toRingHom

/-- The `A ⧸ a`-algebra structure on the completion of
`B ⊗[A] (A ⧸ a)` induced by `includeRight`. -/
instance instAlgebra_includeRight (B : Type u) [CommRing B] [Algebra A B]
    (a : Ideal A) (Ibar : Ideal (A ⧸ a)) :
    Algebra (A ⧸ a)
      (AdicCompletion (tensorIncludeRightIdeal B a Ibar : Ideal (B ⊗[A] (A ⧸ a)))
        (B ⊗[A] (A ⧸ a))) :=
  ((algebraMap (B ⊗[A] (A ⧸ a))
      (AdicCompletion (tensorIncludeRightIdeal B a Ibar : Ideal (B ⊗[A] (A ⧸ a)))
        (B ⊗[A] (A ⧸ a)))).comp
    (Algebra.TensorProduct.includeRight :
      (A ⧸ a) →ₐ[A] B ⊗[A] (A ⧸ a)).toRingHom).toAlgebra

/-- The structure map `A ⧸ a → (B ⊗[A] (A ⧸ a))^∧` factors through
`includeRight`. -/
theorem algebraMap_tensorIncludeRight (B : Type u) [CommRing B] [Algebra A B]
    (a : Ideal A) (Ibar : Ideal (A ⧸ a)) (x : A ⧸ a) :
    algebraMap (A ⧸ a)
        (AdicCompletion (tensorIncludeRightIdeal B a Ibar : Ideal (B ⊗[A] (A ⧸ a)))
          (B ⊗[A] (A ⧸ a))) x =
      algebraMap (B ⊗[A] (A ⧸ a))
        (AdicCompletion (tensorIncludeRightIdeal B a Ibar : Ideal (B ⊗[A] (A ⧸ a)))
          (B ⊗[A] (A ⧸ a)))
        ((Algebra.TensorProduct.includeRight :
            (A ⧸ a) →ₐ[A] B ⊗[A] (A ⧸ a)) x) := sorry

/-- Extending `Ibar` along the tensor-quotient identification recovers the
extension along `includeRight`. -/
theorem quotIdealMap_map_includeRight (a : Ideal A) (Ibar : Ideal (A ⧸ a)) :
    (Ibar.map (algebraMap (A ⧸ a) (B ⧸ a.map (algebraMap A B)))).map
        (Algebra.TensorProduct.quotIdealMapEquivTensorQuot B a).toRingHom =
      tensorIncludeRightIdeal B a Ibar := sorry

/-- The underlying ring identification
`(B ⊗[A] (A ⧸ a))^∧ ≃+* B ⧸ aB` of closed-immersion base change. -/
def closedImmersionBaseChangeRingEquiv (a : Ideal A) (Ibar : Ideal (A ⧸ a))
    [IsAdicComplete (Ibar.map (algebraMap (A ⧸ a) (B ⧸ a.map (algebraMap A B))))
      (B ⧸ a.map (algebraMap A B))] :
    AdicCompletion (tensorIncludeRightIdeal B a Ibar) (B ⊗[A] (A ⧸ a)) ≃+*
      B ⧸ a.map (algebraMap A B) :=
  (ringCongr (Algebra.TensorProduct.quotIdealMapEquivTensorQuot B a).toRingEquiv
        (quotIdealMap_map_includeRight a Ibar)).symm.trans
    (ofAlgEquiv (Ibar.map (algebraMap (A ⧸ a) (B ⧸ a.map (algebraMap A B))))).symm.toRingEquiv

/-- The ring identification of closed-immersion base change commutes with the
`A ⧸ a`-algebra structures. -/
theorem closedImmersionBaseChange_algebraMap (a : Ideal A) (Ibar : Ideal (A ⧸ a))
    [IsAdicComplete (Ibar.map (algebraMap (A ⧸ a) (B ⧸ a.map (algebraMap A B))))
      (B ⧸ a.map (algebraMap A B))]
    (x : A ⧸ a) :
    closedImmersionBaseChangeRingEquiv a Ibar
        (algebraMap (A ⧸ a)
          (AdicCompletion (tensorIncludeRightIdeal B a Ibar) (B ⊗[A] (A ⧸ a))) x) =
      algebraMap (A ⧸ a) (B ⧸ a.map (algebraMap A B)) x := sorry

/-- The completion of `B ⊗[A] (A ⧸ a)` is canonically identified with
`B ⧸ aB` as an `A ⧸ a`-algebra when the quotient is complete. -/
def closedImmersionBaseChange (a : Ideal A) (Ibar : Ideal (A ⧸ a))
    [h_complete : IsAdicComplete (Ibar.map (algebraMap (A ⧸ a) (B ⧸ a.map (algebraMap A B))))
      (B ⧸ a.map (algebraMap A B))] :
    AdicCompletion (tensorIncludeRightIdeal B a Ibar) (B ⊗[A] (A ⧸ a)) ≃ₐ[A ⧸ a]
      B ⧸ a.map (algebraMap A B) :=
  AlgEquiv.ofRingEquiv (closedImmersionBaseChange_algebraMap a Ibar)

/-- The closed-immersion identification sends the dense tensor `b ⊗ₜ r` to
the class of `r • b` in `B ⧸ aB`. -/
theorem closedImmersionBaseChange_of (a : Ideal A) (Ibar : Ideal (A ⧸ a))
    [IsAdicComplete (Ibar.map (algebraMap (A ⧸ a) (B ⧸ a.map (algebraMap A B))))
      (B ⧸ a.map (algebraMap A B))]
    (b : B) (r : A) :
    closedImmersionBaseChange a Ibar
        (of (tensorIncludeRightIdeal B a Ibar) (B ⊗[A] (A ⧸ a))
          (b ⊗ₜ Ideal.Quotient.mk a r)) =
      Ideal.Quotient.mk (a.map (algebraMap A B)) (r • b) := sorry

/-- For an `I`-adically complete algebra `B` with finite-type special fiber over
a Noetherian ring `A`, completion of `B ⊗[A] (A ⧸ a)` along an ideal `Ibar`
cofinal with the image of `I` is canonically equivalent to `B ⧸ aB` as an
`A ⧸ a`-algebra. -/
def closedImmersionBaseChangeOfCofinal (I a : Ideal A)
    [IsNoetherianRing A] [IsAdicComplete I B]
    [Algebra.FiniteType (A ⧸ I) (B ⧸ I.map (algebraMap A B))]
    (Ibar : Ideal (A ⧸ a)) {c d : ℕ} (hc : 0 < c) (hd : 0 < d)
    (hI : I.map (Ideal.Quotient.mk a) ^ c ≤ Ibar)
    (hIbar : Ibar ^ d ≤ I.map (Ideal.Quotient.mk a)) :
    AdicCompletion (tensorIncludeRightIdeal B a Ibar) (B ⊗[A] (A ⧸ a)) ≃ₐ[A ⧸ a]
      B ⧸ a.map (algebraMap A B) :=
  closedImmersionBaseChange a Ibar
    (h_complete := IsAdicComplete.quotIdealMap I a Ibar hc hd hI hIbar)

end AdicCompletion
