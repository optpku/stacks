module

public import stacks_project.Chap10.Lemma_10_143_11.KernelIdealTransport

@[expose] public section

-- Declarations moved out of `Lemma_10_143_11.lean` to keep the active proof file small.

open scoped TensorProduct

universe u v w x

namespace RingHom

section

variable {Aprime : Type u} {A : Type v} {Bprime : Type w} {B : Type x}
variable [CommRing Aprime] [CommRing A] [CommRing Bprime] [CommRing B]
variable (g : Aprime →+* Bprime) (qA : Aprime →+* A) (qB : Bprime →+* B) (f : A →+* B)

/-- Helper for Lemma 10.143.11: the explicit textbook map `IC → J` sends an element to zero
exactly when its underlying ring element lies in the comparison kernel. -/
lemma mapMap_eq_zero_iff
    {R : Type*} [CommRing R] {S : Type*} [CommRing S] {T : Type*} [CommRing T]
    {I : Ideal R} {f : R →+* S} {g : R →+* T} {φ : S →+* T}
    (hcomp : φ.comp f = g) (x : Ideal.map f I) :
    Ideal.mapMap I φ hcomp x = 0 ↔ ((x : Ideal.map f I) : S) ∈ RingHom.ker φ := by
  constructor
  · intro hx
    -- Equality in the subtype target is equality of the underlying ring elements.
    rw [RingHom.mem_ker]
    exact congrArg Subtype.val hx
  · intro hx
    -- Conversely, vanishing in the codomain ring makes the subtype element zero.
    apply Subtype.ext
    rwa [RingHom.mem_ker] at hx

/-- Helper for Lemma 10.143.11: injectivity of the textbook ideal comparison `IC → J`
forces the residual kernel inside `IC` to vanish. -/
lemma inf_eq_bot_of_mapMap_injective
    {R : Type*} [CommRing R] {S : Type*} [CommRing S] {T : Type*} [CommRing T]
    {I : Ideal R} {f : R →+* S} {g : R →+* T} {φ : S →+* T}
    (hcomp : φ.comp f = g)
    (hinj : Function.Injective (Ideal.mapMap I φ hcomp)) :
    RingHom.ker φ ⊓ Ideal.map f I = ⊥ := by
  apply le_antisymm
  · intro x hx
    -- View `x` as an element of `f(I)`, then compare it with zero through injectivity.
    rw [Ideal.mem_bot]
    have hx_zero :
        Ideal.mapMap I φ hcomp ⟨x, hx.2⟩ = 0 := by
      exact (mapMap_eq_zero_iff (I := I) (f := f) (g := g) hcomp ⟨x, hx.2⟩).2 hx.1
    have hx_zero' :
        Ideal.mapMap I φ hcomp ⟨x, hx.2⟩ =
          Ideal.mapMap I φ hcomp 0 := by
      simpa using hx_zero
    have hx_eq : (⟨x, hx.2⟩ : Ideal.map f I) = 0 := hinj hx_zero'
    exact congrArg Subtype.val hx_eq
  · exact bot_le

/-- Helper for Lemma 10.143.11: once the residual comparison kernel inside `IC` is zero, the
kernel term produced by `Ideal.mapCotangent_ker_of_surjective` is also zero. -/
lemma residual_cotangent_kernel_eq_bot_of_inf_eq_bot
    {R : Type*} [CommRing R] (I K : Ideal R)
    (hInf : K ⊓ I = ⊥) :
    (Submodule.comap I.subtype (K ⊓ I)).map (Ideal.toCotangent I) = ⊥ := by
  -- After rewriting the residual ideal to `⊥`, only the zero submodule remains.
  rw [hInf]
  simp

/-- Helper for Lemma 10.143.11: after identifying the source and target quotient kernels with the
textbook ideals, the cotangent comparison induced by `φ` is surjective and its kernel is exactly
the cotangent image of the residual kernel `ker φ ⊆ f(I)`. -/
lemma mapCotangent_surjective_and_ker_eq_residual_of_comp_eq_of_ker_eq
    {R : Type*} [CommRing R] {C : Type*} [CommRing C]
    {B₀ : Type*} [CommRing B₀] {B₁ : Type*} [CommRing B₁]
    [Algebra R C] [Algebra R B₁]
    {I : Ideal R} {qC : C →+* B₀} {qB : B₁ →+* B₀} {φ : C →+* B₁}
    (hSurj : Function.Surjective φ)
    (hq : qB.comp φ = qC)
    (hcomp : φ.comp (algebraMap R C) = algebraMap R B₁)
    (hSrc : RingHom.ker qC = Ideal.map (algebraMap R C) I)
    (hTgt : RingHom.ker qB = Ideal.map (algebraMap R B₁) I) :
    let φAlg : C →ₐ[R] B₁ :=
      { toRingHom := φ
        commutes' := fun r ↦ by
          -- The cotangent comparison uses the same `R`-algebra structure encoded by `hcomp`.
          exact congrArg (fun h : R →+* B₁ ↦ h r) hcomp }
    let hle : Ideal.map (algebraMap R C) I ≤ Ideal.comap φAlg (Ideal.map (algebraMap R B₁) I) :=
      Ideal.map_le_comap_of_comp_eq I φ hcomp
    Function.Surjective
        (Ideal.mapCotangent (Ideal.map (algebraMap R C) I) (Ideal.map (algebraMap R B₁) I)
          φAlg hle) ∧
      LinearMap.ker
          (Ideal.mapCotangent (Ideal.map (algebraMap R C) I) (Ideal.map (algebraMap R B₁) I)
            φAlg hle) =
        ((Submodule.comap (Ideal.map (algebraMap R C) I).subtype (RingHom.ker φ)).map
          (Ideal.toCotangent (Ideal.map (algebraMap R C) I))).restrictScalars R := sorry

/-- Helper for Lemma 10.143.11: a cotangent comparison map is injective once conjugating it by
source and target linear equivalences gives the identity. -/
lemma mapCotangent_injective_of_conjugation_eq_id
    {R : Type*} [CommRing R]
    {A : Type*} [CommRing A] {B : Type*} [CommRing B]
    [Algebra R A] [Algebra R B]
    {I₁ : Ideal A} {I₂ : Ideal B} {f : A →ₐ[R] B}
    (h : I₁ ≤ I₂.comap f)
    {M : Type*} [AddCommGroup M] [Module R M]
    (eSrc : I₁.Cotangent ≃ₗ[R] M) (eTgt : I₂.Cotangent ≃ₗ[R] M)
    (hconj :
      (eTgt.toLinearMap.comp (Ideal.mapCotangent I₁ I₂ f h)).comp eSrc.symm.toLinearMap =
        (LinearMap.id : M →ₗ[R] M)) :
    Function.Injective (Ideal.mapCotangent I₁ I₂ f h) := by
  intro x y hxy
  -- Evaluate the conjugated identity on the two source coordinates and compare through `hxy`.
  apply eSrc.injective
  have hxid :
      ((eTgt.toLinearMap.comp (Ideal.mapCotangent I₁ I₂ f h)).comp eSrc.symm.toLinearMap)
        (eSrc x) =
        eSrc x := by
    exact congrArg (fun l : M →ₗ[R] M ↦ l (eSrc x)) hconj
  have hyid :
      ((eTgt.toLinearMap.comp (Ideal.mapCotangent I₁ I₂ f h)).comp eSrc.symm.toLinearMap)
        (eSrc y) =
        eSrc y := by
    exact congrArg (fun l : M →ₗ[R] M ↦ l (eSrc y)) hconj
  calc
    eSrc x =
        ((eTgt.toLinearMap.comp (Ideal.mapCotangent I₁ I₂ f h)).comp eSrc.symm.toLinearMap)
          (eSrc x) := hxid.symm
    _ = eTgt ((Ideal.mapCotangent I₁ I₂ f h) x) := by
          simp [LinearMap.comp_apply]
    _ = eTgt ((Ideal.mapCotangent I₁ I₂ f h) y) := by rw [hxy]
    _ =
        ((eTgt.toLinearMap.comp (Ideal.mapCotangent I₁ I₂ f h)).comp eSrc.symm.toLinearMap)
          (eSrc y) := by
          simp [LinearMap.comp_apply]
    _ = eSrc y := hyid

/-- Helper for Lemma 10.143.11: if the cotangent comparison for the textbook ideal map becomes
the identity after transport to a common model, then the textbook ideal map itself is injective. -/
lemma mapMap_injective_of_conjugation_eq_id
    {R : Type*} [CommRing R] {S : Type*} [CommRing S] {T : Type*} [CommRing T]
    [Algebra R S] [Algebra R T]
    {I : Ideal R} {φ : S →+* T}
    (hcomp : φ.comp (algebraMap R S) = algebraMap R T)
    (hSrcSq : (Ideal.map (algebraMap R S) I) ^ 2 = ⊥)
    {M : Type*} [AddCommGroup M] [Module R M]
    (eSrc : (Ideal.map (algebraMap R S) I).Cotangent ≃ₗ[R] M)
    (eTgt : (Ideal.map (algebraMap R T) I).Cotangent ≃ₗ[R] M)
    (hconj :
      (eTgt.toLinearMap.comp
          (Ideal.mapCotangent (Ideal.map (algebraMap R S) I) (Ideal.map (algebraMap R T) I)
            { toRingHom := φ
              commutes' := fun x ↦ by
                -- The cotangent comparison uses the same algebra structure as `Ideal.mapMap`.
                exact congrArg (fun h : R →+* T ↦ h x) hcomp }
            (Ideal.map_le_comap_of_comp_eq I φ hcomp))).comp
        eSrc.symm.toLinearMap =
        (LinearMap.id : M →ₗ[R] M)) :
    Function.Injective (Ideal.mapMap I φ hcomp) := by
  -- First upgrade the transported-identity statement to cotangent injectivity.
  have hCotInj :
      Function.Injective
        (Ideal.mapCotangent (Ideal.map (algebraMap R S) I) (Ideal.map (algebraMap R T) I)
          { toRingHom := φ
            commutes' := fun x ↦ by
              -- This is the same `R`-algebra structure encoded by `hcomp`.
              exact congrArg (fun h : R →+* T ↦ h x) hcomp }
          (Ideal.map_le_comap_of_comp_eq I φ hcomp)) :=
    mapCotangent_injective_of_conjugation_eq_id
      (I₁ := Ideal.map (algebraMap R S) I) (I₂ := Ideal.map (algebraMap R T) I)
      (f := { toRingHom := φ
              commutes' := fun x ↦ by
                exact congrArg (fun h : R →+* T ↦ h x) hcomp })
      (h := Ideal.map_le_comap_of_comp_eq I φ hcomp)
      eSrc eTgt hconj
  -- Then reuse the existing square-zero bridge from cotangent injectivity to ideal injectivity.
  exact mapMap_injective_of_mapCotangent_injective
    (R := R) (S := S) (T := T) (I := I) (φ := φ) hcomp hSrcSq hCotInj

/-- Helper for Lemma 10.143.11: once the common model is built at cotangent level, the existing
square-zero identifications convert it into the ideal-level transport identity used for kernels. -/
lemma common_model_ideal_transport_identity_of_cotangent_conjugation_eq_id
    {R : Type*} [CommRing R] {C : Type*} [CommRing C]
    {B₀ : Type*} [CommRing B₀] {B₁ : Type*} [CommRing B₁]
    [Algebra R C] [Algebra R B₁]
    {I : Ideal R} {qC : C →+* B₀} {qB : B₁ →+* B₀} {φAlg : C →ₐ[R] B₁}
    (hq : qB.comp φAlg.toRingHom = qC)
    (hcomp : φAlg.toRingHom.comp (algebraMap R C) = algebraMap R B₁)
    (hSrc : RingHom.ker qC = Ideal.map (algebraMap R C) I)
    (hTgt : RingHom.ker qB = Ideal.map (algebraMap R B₁) I)
    (hSrcSq : (Ideal.map (algebraMap R C) I) ^ 2 = ⊥)
    (hTgtSq : (Ideal.map (algebraMap R B₁) I) ^ 2 = ⊥)
    {M : Type*} [AddCommGroup M] [Module R M]
    (eCotSrc : M ≃ₗ[R] (Ideal.map (algebraMap R C) I).Cotangent)
    (eCotTgt : M ≃ₗ[R] (Ideal.map (algebraMap R B₁) I).Cotangent)
    (hconj :
      (eCotTgt.symm.toLinearMap.comp
          (Ideal.mapCotangent (Ideal.map (algebraMap R C) I) (Ideal.map (algebraMap R B₁) I)
            φAlg
            (Ideal.map_le_comap_of_comp_eq I φAlg.toRingHom hcomp))).comp
        eCotSrc.toLinearMap =
        (LinearMap.id : M →ₗ[R] M)) :
    ∃ (eIdealSrc : M ≃ Ideal.map (algebraMap R C) I)
      (eIdealTgt : M ≃ Ideal.map (algebraMap R B₁) I),
      ∀ x : M,
        eIdealTgt.symm
          ((ideal_equiv_ker qB (Ideal.map (algebraMap R B₁) I) hTgt).symm
            (RingHom.kerMap φAlg.toRingHom hq
              ((eIdealSrc.trans
                (ideal_equiv_ker qC (Ideal.map (algebraMap R C) I) hSrc)) x))) = x := sorry

end

end RingHom
