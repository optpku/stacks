/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import Mathlib.RingTheory.AdicCompletion.Functoriality
public import Mathlib.RingTheory.AdicCompletion.AsTensorProduct
public import Mathlib.RingTheory.AdicCompletion.RingHom
public import Mathlib.RingTheory.Flat.Stability
public import Mathlib.RingTheory.Localization.BaseChange
public import Mathlib.RingTheory.Localization.Finiteness
public import Mathlib.RingTheory.Localization.Submodule
public import Mathlib.RingTheory.Localization.Module
public import Mathlib.RingTheory.TensorProduct.Basic
public import ReasLib.RingTheory.AdicCompletion.LocalizationAway
public import ReasLib.RingTheory.Ideal.Tensor
public import ReasLib.RingTheory.Ideal.BaseChange
public import ReasLib.RingTheory.Completion.Quotient
public import ReasLib.RingTheory.Topology.Adic.Complete

/-!
# Ideals and quotients of completed principal localizations

For a Noetherian ring, tensor products and completed localized modules give canonical
descriptions of an extended ideal. For a complete adic ring and an element invertible
modulo the ideal, the residue quotient is unchanged. A prime ideal therefore extends
to a prime ideal in that case.
-/

@[expose] public section

noncomputable section

open scoped TensorProduct

universe u

namespace completedPrincipalLocalization

variable {A : Type u} [CommRing A] [TopologicalSpace A]
  [TopologicalRing.IsAdicRing A] [IsNoetherianRing A]

/-- The completed localization is flat over the original Noetherian ring. -/
instance moduleFlat (I : Ideal A) (f : A) :
    Module.Flat A (completedPrincipalLocalization I f) :=
  Module.Flat.trans A (Localization.Away f) (completedPrincipalLocalization I f)

omit [IsNoetherianRing A] in
/-- An adic ring is complete for every supplied defining adic ideal. -/
theorem isAdicComplete_definingIdeal (I : Ideal A) (hI : IsAdic I) :
    IsAdicComplete I A := by
  letI : UniformSpace A := IsTopologicalAddGroup.rightUniformSpace A
  letI : IsUniformAddGroup A := isUniformAddGroup_of_addCommGroup
  exact hI.isAdicComplete_iff.mpr ⟨inferInstance, inferInstance⟩

section ResidueStages

omit [TopologicalSpace A] [TopologicalRing.IsAdicRing A] [IsNoetherianRing A]

/-- Localization at an element invertible in the residue ring maps back to that ring. -/
def residueAway (p : Ideal A) (f : A) (hf : IsUnit (Ideal.Quotient.mk p f)) :
    Localization.Away f →ₐ[A] A ⧸ p :=
  IsLocalization.Away.liftAlgHom f
    (f := Ideal.Quotient.mkₐ A p) hf

/-- The residue localization map respects the defining-ideal filtration. -/
theorem residueAway_pow_le (I p : Ideal A) (f : A)
    (hf : IsUnit (Ideal.Quotient.mk p f)) (n : ℕ) :
    (I.map (algebraMap A (Localization.Away f))) ^ n ≤
      ((I.map (Ideal.Quotient.mk p)) ^ n).comap (residueAway p f hf).toRingHom := sorry

/-- The specified residue map at each finite stage of completed localization. -/
def residueStageMap (I p : Ideal A) (f : A)
    (hf : IsUnit (Ideal.Quotient.mk p f)) (n : ℕ) :
    completedPrincipalLocalization I f →+*
      (A ⧸ p) ⧸ (I.map (Ideal.Quotient.mk p)) ^ n :=
  (Ideal.quotientMap ((I.map (Ideal.Quotient.mk p)) ^ n)
    (residueAway p f hf).toRingHom (residueAway_pow_le I p f hf n)).comp
      (AdicCompletion.evalₐ (I.map (algebraMap A (Localization.Away f))) n).toRingHom

/-- The residue stage maps form the required compatible family. -/
theorem residueStageMap_compatible (I p : Ideal A) (f : A)
    (hf : IsUnit (Ideal.Quotient.mk p f)) {m n : ℕ} (hle : m ≤ n) :
    (Ideal.Quotient.factorPow (I.map (Ideal.Quotient.mk p)) hle).comp
      (residueStageMap I p f hf n) = residueStageMap I p f hf m := sorry

end ResidueStages

/-- The completed localization maps to the complete residue ring by its actual finite-stage
maps, followed by the canonical completeness inverse. -/
def residueRetraction (I : Ideal A) (hI : IsAdic I) (p : Ideal A) (f : A)
    (hf : IsUnit (Ideal.Quotient.mk p f)) :
    completedPrincipalLocalization I f →ₐ[A] A ⧸ p := by
  letI : IsAdicComplete I A := isAdicComplete_definingIdeal I hI
  letI : IsAdicComplete (I.map (Ideal.Quotient.mk p)) (A ⧸ p) :=
    IsAdicComplete.quotient I p
  exact
    { toRingHom := IsAdicComplete.liftRingHom (I.map (Ideal.Quotient.mk p))
        (residueStageMap I p f hf) (residueStageMap_compatible I p f hf)
      commutes' := sorry }

/-- The residue retraction extends the original quotient map. -/
@[simp]
theorem residueRetraction_algebraMap (I : Ideal A) (hI : IsAdic I)
    (p : Ideal A) (f : A) (hf : IsUnit (Ideal.Quotient.mk p f)) (a : A) :
    residueRetraction I hI p f hf
        (algebraMap A (completedPrincipalLocalization I f) a) =
      Ideal.Quotient.mk p a := sorry

/-- The residue retraction kills the extended ideal. -/
theorem map_le_ker_residueRetraction (I : Ideal A) (hI : IsAdic I)
    (p : Ideal A) (f : A) (hf : IsUnit (Ideal.Quotient.mk p f)) :
    p.map (algebraMap A (completedPrincipalLocalization I f)) ≤
      RingHom.ker (residueRetraction I hI p f hf).toRingHom := sorry

/-- The quotient inverse is induced by the explicit residue retraction. -/
def residueQuotientInverse (I : Ideal A) (hI : IsAdic I)
    (p : Ideal A) (f : A) (hf : IsUnit (Ideal.Quotient.mk p f)) :
    (completedPrincipalLocalization I f ⧸
      p.map (algebraMap A (completedPrincipalLocalization I f))) →ₐ[A] A ⧸ p :=
  Ideal.Quotient.liftₐ _ (residueRetraction I hI p f hf)
    (map_le_ker_residueRetraction I hI p f hf)

/-- The quotient inverse evaluates a representative using the residue retraction. -/
@[simp]
theorem residueQuotientInverse_mk (I : Ideal A) (hI : IsAdic I)
    (p : Ideal A) (f : A) (hf : IsUnit (Ideal.Quotient.mk p f))
    (x : completedPrincipalLocalization I f) :
    residueQuotientInverse I hI p f hf
        (Ideal.Quotient.mk (p.map (algebraMap A (completedPrincipalLocalization I f))) x) =
      residueRetraction I hI p f hf x := rfl

/-- A prime ideal remains prime in the completed principal localization at an
element that is a unit modulo the ideal. -/
instance map_isPrime (I : Ideal A) [hI : Fact (IsAdic I)] (p : Ideal A) [p.IsPrime]
    (f : A) [hf : Fact (IsUnit (Ideal.Quotient.mk p f))] :
    (p.map (algebraMap A (completedPrincipalLocalization I f))).IsPrime :=
  sorry

/-- Flatness identifies the tensor extension of any ideal with its mapped ideal. -/
def map_ofTensor_linearEquiv (I : Ideal A) (p : Ideal A) (f : A) :
    p ⊗[A] completedPrincipalLocalization I f ≃ₗ[A]
      (p.map (algebraMap A (completedPrincipalLocalization I f))).restrictScalars A :=
  (TensorProduct.comm A p (completedPrincipalLocalization I f)).trans
    ((p.baseChangeEquiv (completedPrincipalLocalization I f)).restrictScalars A)

/-- The tensor comparison sends a pure tensor to multiplication by the image of
its ideal element in the completed principal localization. -/
theorem map_ofTensor_linearEquiv_apply (I : Ideal A) (p : Ideal A) (f : A)
    (x : A) (hx : x ∈ p) (b : completedPrincipalLocalization I f) :
    (map_ofTensor_linearEquiv I p f (⟨x, hx⟩ ⊗ₜ b)).1 = x • b := sorry

/-- The completion of any localized ideal is linearly equivalent to its extension
in the completed principal localization of a Noetherian ring. -/
def localizedCompletion_linearEquiv (I : Ideal A) (p : Ideal A) (f : A) :
    AdicCompletion (I.map (algebraMap A (Localization.Away f)))
        (LocalizedModule.Away f p) ≃ₗ[completedPrincipalLocalization I f]
      p.map (algebraMap A (completedPrincipalLocalization I f)) :=
  (AdicCompletion.ofTensorProductEquivOfFiniteNoetherian
      (I.map (algebraMap A (Localization.Away f))) (LocalizedModule.Away f p)).symm.trans
    (((LocalizedModule.equivTensorProduct (Submonoid.powers f) p).baseChange
        (Localization.Away f) (completedPrincipalLocalization I f) _ _).trans
      ((TensorProduct.AlgebraTensorModule.cancelBaseChange A (Localization.Away f)
          (completedPrincipalLocalization I f) (completedPrincipalLocalization I f) p).trans
        (p.baseChangeEquiv (completedPrincipalLocalization I f))))

/-- The completion comparison acts by completing the localized inclusion of the
ideal into the base ring. -/
theorem localizedCompletion_linearEquiv_apply (I : Ideal A) (p : Ideal A) (f : A)
    (x : AdicCompletion (I.map (algebraMap A (Localization.Away f)))
      (LocalizedModule.Away f p)) :
    (localizedCompletion_linearEquiv I p f x).1 =
      AdicCompletion.map (I.map (algebraMap A (Localization.Away f)))
        (LocalizedModule.map (Submonoid.powers f) p.subtype) x := sorry

/-- A Noetherian adic residue ring is unchanged by completed localization at an element
invertible in that residue ring. -/
def quotient_algEquiv (I : Ideal A) (hI : IsAdic I) (p : Ideal A)
    (f : A) (hf : IsUnit (Ideal.Quotient.mk p f)) :
    (A ⧸ p) ≃ₐ[A]
      completedPrincipalLocalization I f ⧸
        p.map (algebraMap A (completedPrincipalLocalization I f)) :=
  AlgEquiv.ofAlgHom
    (Ideal.quotientMapₐ
      (p.map (algebraMap A (completedPrincipalLocalization I f)))
      (Algebra.ofId A (completedPrincipalLocalization I f))
      Ideal.le_comap_map)
    (residueQuotientInverse I hI p f hf)
    sorry sorry

/-- The quotient comparison sends a residue class to the class of its canonical
image in the completed principal localization. -/
theorem quotient_algEquiv_apply (I : Ideal A) (hI : IsAdic I)
    (p : Ideal A) (f : A) (hf : IsUnit (Ideal.Quotient.mk p f)) (a : A) :
    quotient_algEquiv I hI p f hf (Ideal.Quotient.mk p a) =
      Ideal.Quotient.mk (p.map (algebraMap A (completedPrincipalLocalization I f)))
        (algebraMap A (completedPrincipalLocalization I f) a) := sorry

/-- A Noetherian adic residue ring is identified with its tensor product with completed
localization at an element invertible in the residue ring. -/
def quotient_tensor_algEquiv (I : Ideal A) (hI : IsAdic I)
    (p : Ideal A) (f : A) (hf : IsUnit (Ideal.Quotient.mk p f)) :
    (A ⧸ p) ≃ₐ[A]
      (A ⧸ p) ⊗[A] completedPrincipalLocalization I f :=
  let multiplication : (A ⧸ p) ⊗[A] completedPrincipalLocalization I f →ₐ[A] A ⧸ p :=
    Algebra.TensorProduct.lift (AlgHom.id A (A ⧸ p))
      (residueRetraction I hI p f hf) (fun _ _ ↦ Commute.all _ _)
  AlgEquiv.ofAlgHom
    (Algebra.TensorProduct.includeLeft :
      (A ⧸ p) →ₐ[A]
        (A ⧸ p) ⊗[A] completedPrincipalLocalization I f)
    multiplication sorry sorry

/-- The inverse tensor comparison multiplies by the actual residue retraction. -/
@[simp]
theorem quotient_tensor_algEquiv_symm_tmul (I : Ideal A) (hI : IsAdic I)
    (p : Ideal A) (f : A) (hf : IsUnit (Ideal.Quotient.mk p f))
    (x : A ⧸ p) (b : completedPrincipalLocalization I f) :
    (quotient_tensor_algEquiv I hI p f hf).symm (x ⊗ₜ b) =
      x * residueRetraction I hI p f hf b := sorry

/-- The quotient tensor comparison sends a residue class `x` to `x ⊗ₜ 1`. -/
theorem quotient_tensor_algEquiv_apply (I : Ideal A) (hI : IsAdic I)
    (p : Ideal A) (f : A) (hf : IsUnit (Ideal.Quotient.mk p f))
    (x : A ⧸ p) :
    quotient_tensor_algEquiv I hI p f hf x = x ⊗ₜ (1 : completedPrincipalLocalization I f) :=
  sorry

end completedPrincipalLocalization
