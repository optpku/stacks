module

public import Mathlib.RingTheory.Localization.BaseChange
public import ReasLib.RingTheory.Algebra.TensorProduct.RightAlgebra
public import ReasLib.RingTheory.Localization.AtPrime.Relative

/-!
# Localizations of Tensor Products

This leaf owns the module-level comparison between localization and tensoring
on the right. The ring-level localization statement is Mathlib's
`IsLocalization.tensorProduct_tensorProduct`.
-/

@[expose] public section

universe u v w x y

open scoped TensorProduct

namespace LocalizedModule

section TensorBaseChange

open scoped Algebra.TensorProduct.Right

variable {R : Type u} {S : Type v} {R' : Type w} {S' : Type x}
variable [CommRing R] [CommRing S] [CommRing R'] [CommRing S']
variable [Algebra R S] [Algebra R R'] [Algebra S S'] [Algebra R' S']
variable (W : Submonoid (S ⊗[R] R'))
variable [Algebra (S ⊗[R] R') S']
variable [IsScalarTower S (S ⊗[R] R') S']
variable [IsScalarTower R' (S ⊗[R] R') S']
variable [IsLocalization W S']
variable {M : Type y} [AddCommGroup M] [Module R M] [Module S M]
variable [IsScalarTower R S M]

/-- Tensoring an `S`-module with a localization of `S ⊗[R] R'` is the corresponding
localized module over the pushout.  This is the generic bridge used by local flatness criteria. -/
@[stacks 00MQ "tensor product and pushout localization"]
noncomputable def tensorBaseChangeEquiv :
    S' ⊗[S] M ≃ₗ[R'] LocalizedModule W ((S ⊗[R] R') ⊗[S] M) := by
  let e :
      S' ⊗[S ⊗[R] R'] ((S ⊗[R] R') ⊗[S] M) ≃ₗ[S ⊗[R] R'] S' ⊗[S] M :=
    (TensorProduct.AlgebraTensorModule.cancelBaseChange S (S ⊗[R] R') S' S' M).restrictScalars
      (S ⊗[R] R')
  let f :
      ((S ⊗[R] R') ⊗[S] M) →ₗ[S ⊗[R] R'] S' ⊗[S] M :=
    e.toLinearMap.comp (TensorProduct.mk (S ⊗[R] R') S' ((S ⊗[R] R') ⊗[S] M) 1)
  -- Local instance justification (defeq pin): expose the named composite as the localization map.
  letI : IsLocalizedModule W f := by
    -- Local instance justification (proof-local temporary data): apply localization invariance
    -- under the linear equivalence `e`.
    letI :
        IsLocalizedModule W
          (TensorProduct.mk (S ⊗[R] R') S' ((S ⊗[R] R') ⊗[S] M) 1) :=
      inferInstance
    exact IsLocalizedModule.of_linearEquiv (S := W)
      (f := TensorProduct.mk (S ⊗[R] R') S' ((S ⊗[R] R') ⊗[S] M) 1) e
  exact
    (IsLocalizedModule.linearEquiv W f
      (LocalizedModule.mkLinearMap W ((S ⊗[R] R') ⊗[S] M))).restrictScalars R'

end TensorBaseChange

section TensorProduct

variable {R : Type u} [CommSemiring R]
variable {M : Type v} [AddCommMonoid M] [Module R M]
variable {N : Type w} [AddCommMonoid N] [Module R N]

/-- Localizing both factors of an `R`-module tensor product gives the tensor product of the
localized modules over `Localization S`.  This is the canonical two-sided localization owner;
the one-sided variants are `tensorRightLinearEquiv` and `LocalizedModule.AtPrime` APIs. -/
@[stacks 00DL "localization of a tensor product"]
noncomputable def tensorProductLinearEquiv (S : Submonoid R) :
    LocalizedModule S M ⊗[Localization S] LocalizedModule S N ≃ₗ[Localization S]
      LocalizedModule S (M ⊗[R] N) :=
  let tensorMap := TensorProduct.map (mkLinearMap S M) (mkLinearMap S N)
  IsLocalization.moduleTensorEquiv S (Localization S) (LocalizedModule S M)
      (LocalizedModule S N) ≪≫ₗ
    (IsLocalizedModule.linearEquiv S tensorMap
      (mkLinearMap S (M ⊗[R] N))).extendScalarsOfIsLocalization S (Localization S)

/-- On localized pure tensors, `tensorProductLinearEquiv` multiplies the two denominators. -/
@[simp, stacks 00DL "localization of a tensor product on pure tensors"]
theorem tensorProductLinearEquiv_apply_mk_tmul_mk (S : Submonoid R)
    (m : M) (n : N) (s t : S) :
    tensorProductLinearEquiv S
        (mk m s ⊗ₜ[Localization S] mk n t) =
      mk (m ⊗ₜ[R] n) (s * t) := sorry

end TensorProduct

variable {R : Type u} [CommSemiring R]
variable {A : Type v} [CommSemiring A] [Algebra R A]

/-- Localizing an `A`-module `X` and then tensoring over `R` with `Q` agrees with localizing
`X ⊗[R] Q`.  This is the right-tensor orientation, with the localized `A`-module as the left
factor. -/
@[stacks 00HT "localization of a right tensor product"]
noncomputable def tensorRightLinearEquiv
    (T : Submonoid A) {X : Type*} [AddCommMonoid X] [Module R X] [Module A X]
    [IsScalarTower R A X] (Q : Type*) [AddCommMonoid Q] [Module R Q] :
    LocalizedModule T X ⊗[R] Q ≃ₗ[A] LocalizedModule T (X ⊗[R] Q) :=
  IsLocalizedModule.linearEquiv T
    (TensorProduct.AlgebraTensorModule.rTensor R Q (LocalizedModule.mkLinearMap T X))
    (LocalizedModule.mkLinearMap T (X ⊗[R] Q))

end LocalizedModule

namespace LocalizedModule.AtPrime

variable {R : Type u} [CommSemiring R]
variable {A : Type v} [CommSemiring A] [Algebra R A]

/-- Localizing an `A`-module at `q` and an `R`-module at the contracted prime `q.under R`
commutes with their tensor product over `R`.  The relative localization actions needed for the
construction remain encapsulated in this data owner. -/
@[stacks 00HT "tensor product localized over an under-prime"]
noncomputable def tensorProductUnderLinearEquiv
    {X : Type*} [AddCommMonoid X] [Module R X] [Module A X] [IsScalarTower R A X]
    (Q : Type*) [AddCommMonoid Q] [Module R Q] (q : PrimeSpectrum A) :
    LocalizedModule.AtPrime q.asIdeal X ⊗[R]
      LocalizedModule.AtPrime (q.asIdeal.under R) Q ≃ₗ[R]
      LocalizedModule.AtPrime q.asIdeal (X ⊗[R] Q) := by
  let p : Ideal R := q.asIdeal.under R
  -- Local instance justification (noncanonical choice): use the relative localization action
  -- associated to the fixed prime `q` only inside this comparison.
  letI : Module (Localization.AtPrime p) (LocalizedModule.AtPrime q.asIdeal X) :=
    Localization.AtPrime.Relative.algebraMapModule (R := R) (M := X) q.asIdeal
  -- Local instance justification (proof-local temporary data): record compatibility of the
  -- relative localization action for the following tensor reassociations.
  letI : IsScalarTower R (Localization.AtPrime p) (LocalizedModule.AtPrime q.asIdeal X) :=
    Localization.AtPrime.Relative.algebraMapModule_isScalarTower
      (R := R) (S := A) (M := X) q.asIdeal
  let eLocalizedRight :
      LocalizedModule.AtPrime q.asIdeal X ⊗[R] LocalizedModule.AtPrime p Q ≃ₗ[R]
        LocalizedModule.AtPrime q.asIdeal X ⊗[R] (Localization.AtPrime p ⊗[R] Q) :=
    TensorProduct.congr (LinearEquiv.refl R _)
      (LinearEquiv.restrictScalars R (LocalizedModule.equivTensorProduct p.primeCompl Q))
  let eAssoc :
      LocalizedModule.AtPrime q.asIdeal X ⊗[R] (Localization.AtPrime p ⊗[R] Q) ≃ₗ[R]
        (LocalizedModule.AtPrime q.asIdeal X ⊗[R] Localization.AtPrime p) ⊗[R] Q :=
    (TensorProduct.assoc R (LocalizedModule.AtPrime q.asIdeal X)
      (Localization.AtPrime p) Q).symm
  let eCancel :
      LocalizedModule.AtPrime q.asIdeal X ⊗[R] Localization.AtPrime p ≃ₗ[R]
        LocalizedModule.AtPrime q.asIdeal X :=
    (TensorProduct.comm R (LocalizedModule.AtPrime q.asIdeal X) (Localization.AtPrime p)).trans
      (LinearEquiv.restrictScalars R <|
        IsLocalization.moduleLid (S := p.primeCompl) (A := Localization.AtPrime p)
          (M₁ := LocalizedModule.AtPrime q.asIdeal X))
  let eCancelRight :
      (LocalizedModule.AtPrime q.asIdeal X ⊗[R] Localization.AtPrime p) ⊗[R] Q ≃ₗ[R]
        LocalizedModule.AtPrime q.asIdeal X ⊗[R] Q :=
    TensorProduct.congr eCancel (LinearEquiv.refl R Q)
  let eLocalizeTensor :
      LocalizedModule.AtPrime q.asIdeal X ⊗[R] Q ≃ₗ[R]
        LocalizedModule.AtPrime q.asIdeal (X ⊗[R] Q) :=
    LinearEquiv.restrictScalars R <|
      LocalizedModule.tensorRightLinearEquiv (R := R) (A := A) (X := X)
        q.asIdeal.primeCompl Q
  exact eLocalizedRight.trans <| eAssoc.trans <| eCancelRight.trans eLocalizeTensor

end LocalizedModule.AtPrime
