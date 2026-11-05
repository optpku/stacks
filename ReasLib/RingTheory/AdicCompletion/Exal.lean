/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import Mathlib.RingTheory.AdicCompletion.Algebra
public import Mathlib.RingTheory.AdicCompletion.Functoriality
public import Mathlib.RingTheory.FiniteType
public import ReasLib.RingTheory.AdicCompletion.Exactness.ShortComplex
public import ReasLib.RingTheory.AdicCompletion.FilteredAdditive
public import ReasLib.RingTheory.AdicCompletion.Map
public import ReasLib.RingTheory.Extension.SquareZero
public import Mathlib.RingTheory.Smooth.Locus

/-!
# Adic completion of square-zero algebra extensions

Completion along the inverse-image ideal induces a map on cotangent extension
classes. For a finite type algebra over a field, smooth off the closed subset,
this map is bijective for finite coefficients.
-/

@[expose] public section
noncomputable section
universe u
open Algebra Algebra.Generators Algebra.Extension
open RingHom RingHom.AdicContinuous AdicCompletion CategoryTheory
namespace Algebra.SquareZeroAlgExtension
variable {A B N : Type u} [CommRing A] [CommRing B] [Algebra A B]
variable [AddCommGroup N] [Module B N]

/-- Inverse image of `J` along the projection of a square-zero extension. -/
def adicCompletionIdeal (e : SquareZeroAlgExtension A B N) (J : Ideal B) :
    @Ideal e.carrier e.commRing.toSemiring :=
  -- Local instance justification (proof-local temporary data): unpack bundled `commRing` so `Ideal.comap` on `e.toB` can elaborate.
  letI := e.commRing
  -- Local instance justification (proof-local temporary data): unpack bundled `algebra` so `e.toB` elaborates as an algebra homomorphism.
  letI := e.algebra
  Ideal.comap e.toB.toRingHom J

/-- `adicCompletionIdeal` is the preimage of `J` along the projection. -/
theorem adicCompletionIdeal_eq_comap (e : SquareZeroAlgExtension A B N) (J : Ideal B) :
    (adicCompletionIdeal e J : Set e.carrier) = e.toB ⁻¹' (J : Set B) := rfl

/-- Membership in `adicCompletionIdeal e J` is membership of the image in `J`. -/
theorem mem_adicCompletionIdeal (e : SquareZeroAlgExtension A B N) (J : Ideal B)
    {x : e.carrier} :
    x ∈ adicCompletionIdeal e J ↔ e.toB x ∈ J := Iff.rfl

/-- When the image ideals agree, completion is computed at the same finite
quotient level on both sides; no continuity exponent needs to be selected. -/
private def adicCompletionRingMap {R S : Type u} [CommRing R] [CommRing S]
    (f : R →+* S) (I : Ideal R) (J : Ideal S) (hIJ : Ideal.map f I = J) :
    AdicCompletion I R →+* AdicCompletion J S :=
  let hpow (n : ℕ) : I ^ n ≤ (J ^ n).comap f :=
    Ideal.map_le_iff_le_comap.mp (by rw [Ideal.map_pow, hIJ])
  AdicCompletion.liftRingHom J
    (fun n => (Ideal.quotientMap (J ^ n) f (hpow n)).comp (AdicCompletion.evalₐ I n))
    (by
      intro m n h
      ext x
      induction x using AdicCompletion.induction_on I R with
      | _ a =>
        change Ideal.Quotient.mk (J ^ m) (f (a n)) = Ideal.Quotient.mk (J ^ m) (f (a m))
        apply Ideal.Quotient.eq.mpr
        rw [← map_sub]
        apply hpow m
        change a.val n - a.val m ∈ I ^ m
        simpa only [smul_eq_mul, Ideal.mul_top] using SModEq.sub_mem.mp (a.property h).symm)

private def adicCompletionProjectionRing (e : SquareZeroAlgExtension A B N) (J : Ideal B) :
  -- Local instance justification (proof-local temporary data): unpack the stored middle ring.
  letI := e.commRing
  -- Local instance justification (proof-local temporary data): unpack its stored base algebra.
  letI := e.algebra
  -- Local instance justification (proof-local temporary data): unpack its stored square-zero projection.
  letI := e.isSquareZero
  let I : Ideal e.carrier := adicCompletionIdeal e J
  AdicCompletion I e.carrier →+* AdicCompletion J B :=
  -- Local instance justification (proof-local temporary data): unpack the stored middle ring.
  letI := e.commRing
  -- Local instance justification (proof-local temporary data): unpack its stored base algebra.
  letI := e.algebra
  -- Local instance justification (proof-local temporary data): unpack its stored square-zero projection.
  letI := e.isSquareZero
  let I : Ideal e.carrier := adicCompletionIdeal e J
  adicCompletionRingMap e.toB.toRingHom I J
    (Ideal.map_comap_of_surjective e.toB.toRingHom e.isSquareZero.surjective J)

private theorem adicCompletion_projection_commutes (e : SquareZeroAlgExtension A B N) (J : Ideal B) :
  -- Local instance justification (proof-local temporary data): unpack the stored middle ring.
  letI := e.commRing
  -- Local instance justification (proof-local temporary data): unpack its stored base algebra.
  letI := e.algebra
  -- Local instance justification (proof-local temporary data): unpack its stored square-zero projection.
  letI := e.isSquareZero
  let I : Ideal e.carrier := adicCompletionIdeal e J
  ∀ a : A, adicCompletionProjectionRing e J (algebraMap A (AdicCompletion I e.carrier) a) =
    algebraMap A (AdicCompletion J B) a := by
  letI := e.commRing
  letI := e.algebra
  letI := e.isSquareZero
  let I : Ideal e.carrier := adicCompletionIdeal e J
  change ∀ a : A, adicCompletionProjectionRing e J
    (algebraMap A (AdicCompletion I e.carrier) a) = algebraMap A (AdicCompletion J B) a
  intro a
  apply AdicCompletion.ext_evalₐ
  intro n
  change Ideal.Quotient.mk (J ^ n) (e.toB (algebraMap A e.carrier a)) =
    Ideal.Quotient.mk (J ^ n) (algebraMap A B a)
  exact congrArg (Ideal.Quotient.mk (J ^ n)) (e.toB.commutes a)

private def adicCompletionProjection (e : SquareZeroAlgExtension A B N) (J : Ideal B) :
  -- Local instance justification (proof-local temporary data): unpack the stored middle ring.
  letI := e.commRing
  -- Local instance justification (proof-local temporary data): unpack its stored base algebra.
  letI := e.algebra
  -- Local instance justification (proof-local temporary data): unpack its stored square-zero projection.
  letI := e.isSquareZero
  let I : Ideal e.carrier := adicCompletionIdeal e J
  AdicCompletion I e.carrier →ₐ[A] AdicCompletion J B :=
  -- Local instance justification (proof-local temporary data): unpack the stored middle ring.
  letI := e.commRing
  -- Local instance justification (proof-local temporary data): unpack its stored base algebra.
  letI := e.algebra
  -- Local instance justification (proof-local temporary data): unpack its stored square-zero projection.
  letI := e.isSquareZero
  { toRingHom := adicCompletionProjectionRing e J
    commutes' := adicCompletion_projection_commutes e J }

variable [IsNoetherianRing B] [Module.Finite B N]

private def adicCompletionKernelIncl (e : SquareZeroAlgExtension A B N) (J : Ideal B) :
  -- Local instance justification (proof-local temporary data): unpack the stored middle ring.
  letI := e.commRing
  -- Local instance justification (proof-local temporary data): unpack its stored base algebra.
  letI := e.algebra
  -- Local instance justification (proof-local temporary data): unpack its stored square-zero projection.
  letI := e.isSquareZero
  let I : Ideal e.carrier := adicCompletionIdeal e J
  AdicCompletion I (RingHom.ker e.toB.toRingHom) → AdicCompletion I e.carrier :=
  -- Local instance justification (proof-local temporary data): unpack the stored middle ring.
  letI := e.commRing
  -- Local instance justification (proof-local temporary data): unpack its stored base algebra.
  letI := e.algebra
  -- Local instance justification (proof-local temporary data): unpack its stored square-zero projection.
  letI := e.isSquareZero
  let I : Ideal e.carrier := adicCompletionIdeal e J
  AdicCompletion.map I (Submodule.subtype (RingHom.ker e.toB.toRingHom))

/-- The finite square-zero kernel and the Noetherian quotient make the middle ring
Noetherian, so mathlib's exactness theorem applies to its completion. -/
private theorem adicCompletion_noetherian_source
    (e : SquareZeroAlgExtension A B N) :
    letI := e.commRing
    letI := e.algebra
    IsNoetherianRing e.carrier := by
  letI := e.commRing
  letI := e.algebra
  letI := e.isSquareZero
  letI : Module e.carrier B := Module.compHom B e.toB.toRingHom
  letI : RingHomSurjective e.toB.toRingHom := ⟨e.isSquareZero.surjective⟩
  let K := Ideal.Cotangent (RingHom.ker e.toB.toRingHom)
  have hsmul (a : e.carrier) (y : K) : e.toB.toRingHom a • y = a • y := by
    change (e.toB.toRingHom.quotientKerEquivOfSurjective
      e.isSquareZero.surjective).symm (e.toB.toRingHom a) • y = a • y
    rw [RingHom.quotientKerEquivOfSurjective_symm_apply (f := e.toB.toRingHom)
      e.isSquareZero.surjective a]
    exact IsScalarTower.algebraMap_smul
      (e.carrier ⧸ RingHom.ker e.toB.toRingHom) a y
  let f : K →ₛₗ[e.toB.toRingHom] K :=
    { toFun := _root_.id
      map_add' := fun _ _ => rfl
      map_smul' := fun a y => (hsmul a y).symm }
  letI : IsNoetherian B K := e.kernelEquiv.isNoetherian_iff.mpr inferInstance
  letI : IsNoetherian e.carrier K :=
    (f.isNoetherian_iff_of_bijective Function.bijective_id).mpr inferInstance
  letI : IsNoetherian e.carrier (RingHom.ker e.toB.toRingHom) :=
    (RingHom.SquareZeroExtension.toCotangentEquiv_source e.toB.toRingHom).isNoetherian_iff.mpr
      inferInstance
  let g : B →ₛₗ[e.toB.toRingHom] B :=
    { toFun := _root_.id
      map_add' := fun _ _ => rfl
      map_smul' := fun _ _ => rfl }
  letI : IsNoetherian e.carrier B :=
    (g.isNoetherian_iff_of_bijective Function.bijective_id).mpr inferInstance
  let p : e.carrier →ₗ[e.carrier] B :=
    { toFun := e.toB
      map_add' := map_add e.toB
      map_smul' := fun a x => map_mul e.toB a x }
  exact isNoetherian_of_range_eq_ker (Submodule.subtype (RingHom.ker e.toB.toRingHom)) p
    (by rw [Submodule.range_subtype]; rfl)

private theorem adicCompletion_scalar_filtration
    {R S : Type u} [CommRing R] [CommRing S]
    (f : R →+* S) (hf : Function.Surjective f) (I : Ideal R) (J : Ideal S)
    (hIJ : Ideal.map f I = J) :
    letI := f.toAlgebra
    ∀ n (b : S), b ∈ I ^ n • (⊤ : Submodule R S) ↔ b ∈ J ^ n := by
  letI := f.toAlgebra
  let p := Algebra.linearMap R S
  have hrange : LinearMap.range p = ⊤ := LinearMap.range_eq_top.mpr hf
  have hmap (n : ℕ) : Ideal.map f (I ^ n) = J ^ n := by
    rw [Ideal.map_pow, hIJ]
  intro n b
  have hmod : Submodule.map p (I ^ n • (⊤ : Submodule R R)) =
      I ^ n • (⊤ : Submodule R S) := by
    rw [Submodule.map_smul'', Submodule.map_top, hrange]
  rw [← hmod, Submodule.mem_map, ← hmap n, Ideal.mem_map_iff_of_surjective f hf]
  simp only [smul_eq_mul, Ideal.mul_top]
  rfl

/-- Surjectivity follows by lifting a Cauchy sequence through the original
surjection, after identifying the scalar filtrations. -/
private theorem adicCompletion_ringMap_surjective
    {R S : Type u} [CommRing R] [CommRing S]
    (f : R →+* S) (hf : Function.Surjective f) (I : Ideal R) (J : Ideal S)
    (hIJ : Ideal.map f I = J) :
    Function.Surjective (adicCompletionRingMap f I J hIJ) := by
  letI := f.toAlgebra
  have hpow := adicCompletion_scalar_filtration f hf I J hIJ
  intro x
  induction x using AdicCompletion.induction_on J S with
  | _ a =>
    let a' : AdicCauchySequence I S := ⟨a.val, by
      intro m n h
      apply SModEq.sub_mem.mpr
      apply (hpow m _).mpr
      simpa only [smul_eq_mul, Ideal.mul_top] using SModEq.sub_mem.mp (a.property h)⟩
    obtain ⟨z, hz⟩ := AdicCompletion.map_surjective I
      (f := Algebra.linearMap R S) hf (AdicCompletion.mk I S a')
    refine ⟨z, ?_⟩
    induction z using AdicCompletion.induction_on I R with
    | _ b =>
      apply AdicCompletion.ext_evalₐ
      intro n
      have hzn := congrArg (fun w : AdicCompletion I S => w.val n) hz
      change Submodule.Quotient.mk (p := I ^ n • (⊤ : Submodule R S)) (f (b n)) =
        Submodule.Quotient.mk (p := I ^ n • (⊤ : Submodule R S)) (a n) at hzn
      change Ideal.Quotient.mk (J ^ n) (f (b n)) = Ideal.Quotient.mk (J ^ n) (a n)
      apply Ideal.Quotient.eq.mpr
      exact (hpow n _).mp ((Submodule.Quotient.eq _).mp hzn)

/-- The ring completion map and the module completion map have the same kernel.
This only uses surjectivity and the equality of the image ideals. -/
private theorem adicCompletion_completionMap_eq_zero_iff
    {R S : Type u} [CommRing R] [CommRing S]
    (f : R →+* S) (hf : Function.Surjective f) (I : Ideal R) (J : Ideal S)
    (hIJ : Ideal.map f I = J) :
    letI := f.toAlgebra
    ∀ x : AdicCompletion I R,
      adicCompletionRingMap f I J hIJ x = 0 ↔ AdicCompletion.map I (Algebra.linearMap R S) x = 0 := by
  letI := f.toAlgebra
  have hpow := adicCompletion_scalar_filtration f hf I J hIJ
  intro x
  induction x using AdicCompletion.induction_on I R with
  | _ a =>
    have heval (n : ℕ) :
        AdicCompletion.evalₐ J n (adicCompletionRingMap f I J hIJ (AdicCompletion.mk I R a)) =
          Ideal.Quotient.mk (J ^ n) (f (a n)) := rfl
    constructor
    · intro hz
      apply Subtype.ext
      funext n
      change Submodule.Quotient.mk (p := I ^ n • (⊤ : Submodule R S)) (f (a n)) = 0
      rw [Submodule.Quotient.mk_eq_zero]
      apply (hpow n _).mpr
      apply Ideal.Quotient.eq_zero_iff_mem.mp
      rw [← heval, hz, _root_.map_zero]
    · intro hz
      apply AdicCompletion.ext_evalₐ
      intro n
      rw [_root_.map_zero, heval]
      apply Ideal.Quotient.eq_zero_iff_mem.mpr
      apply (hpow n _).mp
      rw [← Submodule.Quotient.mk_eq_zero]
      exact congrArg (fun w : AdicCompletion I S => w.val n) hz

private theorem adicCompletion_kernelMap_mem (e : SquareZeroAlgExtension A B N) (J : Ideal B) :
  -- Local instance justification (proof-local temporary data): unpack the stored middle ring.
  letI := e.commRing
  -- Local instance justification (proof-local temporary data): unpack its stored base algebra.
  letI := e.algebra
  -- Local instance justification (proof-local temporary data): unpack its stored square-zero projection.
  letI := e.isSquareZero
  let I : Ideal e.carrier := adicCompletionIdeal e J
  ∀ z : AdicCompletion I (RingHom.ker e.toB.toRingHom),
    adicCompletionKernelIncl e J z ∈ RingHom.ker (adicCompletionProjection e J).toRingHom := by
  letI := e.commRing
  letI := e.algebra
  letI := e.isSquareZero
  let I : Ideal e.carrier := adicCompletionIdeal e J
  letI : Module e.carrier B := Module.compHom B e.toB.toRingHom
  let p : e.carrier →ₗ[e.carrier] B :=
    { toFun := e.toB
      map_add' := map_add e.toB
      map_smul' := fun r x => map_mul e.toB r x }
  change ∀ z : AdicCompletion I (RingHom.ker e.toB.toRingHom),
    adicCompletionProjectionRing e J (adicCompletionKernelIncl e J z) = 0
  intro z
  apply (adicCompletion_completionMap_eq_zero_iff e.toB.toRingHom
    e.isSquareZero.surjective I J
    (Ideal.map_comap_of_surjective e.toB.toRingHom e.isSquareZero.surjective J)
    _).mpr
  change AdicCompletion.map I p
    (AdicCompletion.map I (Submodule.subtype (RingHom.ker e.toB.toRingHom)) z) = 0
  rw [AdicCompletion.map_comp_apply]
  have hzero : p.comp (Submodule.subtype (RingHom.ker e.toB.toRingHom)) = 0 := by
    ext y
    exact y.2
  rw [hzero, AdicCompletion.map_zero, LinearMap.zero_apply]

private def adicCompletionKernelMap (e : SquareZeroAlgExtension A B N) (J : Ideal B) :
  -- Local instance justification (proof-local temporary data): unpack the stored middle ring.
  letI := e.commRing
  -- Local instance justification (proof-local temporary data): unpack its stored base algebra.
  letI := e.algebra
  -- Local instance justification (proof-local temporary data): unpack its stored square-zero projection.
  letI := e.isSquareZero
  let I : Ideal e.carrier := adicCompletionIdeal e J
  AdicCompletion I (RingHom.ker e.toB.toRingHom) →
    RingHom.ker (adicCompletionProjection e J).toRingHom :=
  -- Local instance justification (proof-local temporary data): unpack the stored middle ring.
  letI := e.commRing
  -- Local instance justification (proof-local temporary data): unpack its stored base algebra.
  letI := e.algebra
  -- Local instance justification (proof-local temporary data): unpack its stored square-zero projection.
  letI := e.isSquareZero
  let I : Ideal e.carrier := adicCompletionIdeal e J
  fun z ↦ ⟨adicCompletionKernelIncl e J z, adicCompletion_kernelMap_mem e J z⟩

private theorem adicCompletion_kernelMap_bijective (e : SquareZeroAlgExtension A B N) (J : Ideal B) :
  -- Local instance justification (proof-local temporary data): unpack the stored middle ring.
  letI := e.commRing
  -- Local instance justification (proof-local temporary data): unpack its stored base algebra.
  letI := e.algebra
  -- Local instance justification (proof-local temporary data): unpack its stored square-zero projection.
  letI := e.isSquareZero
  Function.Bijective (adicCompletionKernelMap e J) := by
  letI := e.commRing
  letI := e.algebra
  letI := e.isSquareZero
  letI : IsNoetherianRing e.carrier := adicCompletion_noetherian_source e
  let I : Ideal e.carrier := adicCompletionIdeal e J
  letI : Module e.carrier B := Module.compHom B e.toB.toRingHom
  let p : e.carrier →ₗ[e.carrier] B :=
    { toFun := e.toB
      map_add' := map_add e.toB
      map_smul' := fun r x => map_mul e.toB r x }
  let i := Submodule.subtype (RingHom.ker e.toB.toRingHom)
  have hi : Function.Injective i := Subtype.val_injective
  have hex : Function.Exact i p := LinearMap.exact_subtype_ker_map p
  have hp : Function.Surjective p := e.isSquareZero.surjective
  constructor
  · intro x y hxy
    apply AdicCompletion.map_injective I hi
    exact congrArg Subtype.val hxy
  · intro x
    have hx : AdicCompletion.map I p x.val = 0 :=
      (adicCompletion_completionMap_eq_zero_iff e.toB.toRingHom
        e.isSquareZero.surjective I J
        (Ideal.map_comap_of_surjective e.toB.toRingHom e.isSquareZero.surjective J)
        x.val).mp x.property
    obtain ⟨z, hz⟩ := (AdicCompletion.map_exact hi hex hp x.val).mp hx
    exact ⟨z, Subtype.ext hz⟩

private theorem adicCompletion_projection_isSquareZero (e : SquareZeroAlgExtension A B N) (J : Ideal B) :
  -- Local instance justification (proof-local temporary data): unpack the stored middle ring.
  letI := e.commRing
  -- Local instance justification (proof-local temporary data): unpack its stored base algebra.
  letI := e.algebra
  -- Local instance justification (proof-local temporary data): unpack its stored square-zero projection.
  letI := e.isSquareZero
  let I : Ideal e.carrier := adicCompletionIdeal e J
  (adicCompletionProjection e J).toRingHom.IsSquareZeroExtension := by
  letI := e.commRing
  letI := e.algebra
  letI := e.isSquareZero
  let I : Ideal e.carrier := adicCompletionIdeal e J
  constructor
  · exact adicCompletion_ringMap_surjective e.toB.toRingHom e.isSquareZero.surjective I J
      (Ideal.map_comap_of_surjective e.toB.toRingHom e.isSquareZero.surjective J)
  · apply le_antisymm _ bot_le
    rw [pow_two]
    apply Ideal.mul_le.mpr
    intro x hx y hy
    change x * y = 0
    obtain ⟨a, ha⟩ := (adicCompletion_kernelMap_bijective e J).surjective ⟨x, hx⟩
    obtain ⟨b, hb⟩ := (adicCompletion_kernelMap_bijective e J).surjective ⟨y, hy⟩
    have ha' : adicCompletionKernelIncl e J a = x := congrArg Subtype.val ha
    have hb' : adicCompletionKernelIncl e J b = y := congrArg Subtype.val hb
    rw [← ha', ← hb']
    apply Subtype.ext
    funext n
    change (AdicCompletion.map I (Submodule.subtype (RingHom.ker e.toB.toRingHom)) a).val n *
      (AdicCompletion.map I (Submodule.subtype (RingHom.ker e.toB.toRingHom)) b).val n = 0
    rw [AdicCompletion.map_val_apply, AdicCompletion.map_val_apply]
    induction a.val n using Quotient.inductionOn' with
    | h a =>
      induction b.val n using Quotient.inductionOn' with
      | h b =>
        change Submodule.Quotient.mk (p := I ^ n • (⊤ : Ideal e.carrier)) (a.val * b.val) = 0
        have hab : a.val * b.val = 0 := by
          apply (Submodule.mem_bot e.carrier).mp
          rw [← e.isSquareZero.ker_sq_eq_bot, pow_two]
          exact Ideal.mul_mem_mul a.property b.property
        rw [hab]
        rfl

private theorem adicCompletion_cotangent_filtration (e : SquareZeroAlgExtension A B N) (J : Ideal B) :
  -- Local instance justification (proof-local temporary data): unpack the stored middle ring.
  letI := e.commRing
  -- Local instance justification (proof-local temporary data): unpack its stored base algebra.
  letI := e.algebra
  -- Local instance justification (proof-local temporary data): unpack its stored square-zero projection.
  letI := e.isSquareZero
  let I : Ideal e.carrier := adicCompletionIdeal e J
  ∀ n (x : Ideal.Cotangent (RingHom.ker e.toB.toRingHom)),
    x ∈ (I ^ n • (⊤ : Submodule e.carrier (Ideal.Cotangent (RingHom.ker e.toB.toRingHom)))) →
    x ∈ (J ^ n • (⊤ : Submodule B (Ideal.Cotangent (RingHom.ker e.toB.toRingHom)))) := by
  letI := e.commRing
  letI := e.algebra
  letI := e.isSquareZero
  let I : Ideal e.carrier := adicCompletionIdeal e J
  change ∀ n (x : Ideal.Cotangent (RingHom.ker e.toB.toRingHom)),
    x ∈ I ^ n • (⊤ : Submodule e.carrier _) → x ∈ J ^ n • (⊤ : Submodule B _)
  intro n x hx
  have hmap : Ideal.map e.toB.toRingHom (I ^ n) = J ^ n := by
    rw [Ideal.map_pow]
    congr 1
    exact Ideal.map_comap_of_surjective e.toB.toRingHom e.isSquareZero.surjective J
  refine Submodule.smul_induction_on hx ?_ ?_
  · intro r hr y _
    have hsmul : e.toB.toRingHom r • y = r • y := by
      change (e.toB.toRingHom.quotientKerEquivOfSurjective
        e.isSquareZero.surjective).symm (e.toB.toRingHom r) • y = r • y
      rw [RingHom.quotientKerEquivOfSurjective_symm_apply (f := e.toB.toRingHom)
        e.isSquareZero.surjective r]
      exact IsScalarTower.algebraMap_smul
        (e.carrier ⧸ RingHom.ker e.toB.toRingHom) r y
    rw [← hsmul]
    apply Submodule.smul_mem_smul _ Submodule.mem_top
    rw [← hmap]
    exact Ideal.mem_map_of_mem _ hr
  · intro y z hy hz
    exact Submodule.add_mem _ hy hz

private def adicCompletionKernelValue (e : SquareZeroAlgExtension A B N) (J : Ideal B) :
  -- Local instance justification (proof-local temporary data): unpack the stored middle ring.
  letI := e.commRing
  -- Local instance justification (proof-local temporary data): unpack its stored base algebra.
  letI := e.algebra
  -- Local instance justification (proof-local temporary data): unpack its stored square-zero projection.
  letI := e.isSquareZero
  -- Local instance justification (proof-local temporary data): unpack square-zero evidence for the completed projection.
  letI := adicCompletion_projection_isSquareZero e J
  Ideal.Cotangent (RingHom.ker (adicCompletionProjection e J).toRingHom) → AdicCompletion J N :=
  -- Local instance justification (proof-local temporary data): unpack the stored middle ring.
  letI := e.commRing
  -- Local instance justification (proof-local temporary data): unpack its stored base algebra.
  letI := e.algebra
  -- Local instance justification (proof-local temporary data): unpack its stored square-zero projection.
  letI := e.isSquareZero
  let I : Ideal e.carrier := adicCompletionIdeal e J
  -- Local instance justification (proof-local temporary data): unpack square-zero evidence for the completed projection.
  letI := adicCompletion_projection_isSquareZero e J
  fun x ↦
    let xKer := (RingHom.SquareZeroExtension.toCotangentEquiv_source
      (adicCompletionProjection e J).toRingHom).symm x
    let z := (Equiv.ofBijective (adicCompletionKernelMap e J)
      (adicCompletion_kernelMap_bijective e J)).symm xKer
    let zCot := AdicCompletion.map I (Ideal.toCotangent (RingHom.ker e.toB.toRingHom)) z
    let zCotJ := FilteredAdditiveCompletion.map I J
      (AddMonoidHom.id (Ideal.Cotangent (RingHom.ker e.toB.toRingHom)))
      (adicCompletion_cotangent_filtration e J) zCot
    AdicCompletion.map J e.kernelEquiv.toLinearMap zCotJ

private theorem adicCompletion_kernelValue_add (e : SquareZeroAlgExtension A B N) (J : Ideal B) :
  -- Local instance justification (proof-local temporary data): unpack the stored middle ring.
  letI := e.commRing
  -- Local instance justification (proof-local temporary data): unpack its stored base algebra.
  letI := e.algebra
  -- Local instance justification (proof-local temporary data): unpack its stored square-zero projection.
  letI := e.isSquareZero
  let I : Ideal e.carrier := adicCompletionIdeal e J
  -- Local instance justification (proof-local temporary data): unpack square-zero evidence for the completed projection.
  letI := adicCompletion_projection_isSquareZero e J
  ∀ x y, adicCompletionKernelValue e J (x + y) =
    adicCompletionKernelValue e J x + adicCompletionKernelValue e J y := sorry

private theorem adicCompletion_kernelValue_smul (e : SquareZeroAlgExtension A B N) (J : Ideal B) :
  -- Local instance justification (proof-local temporary data): unpack the stored middle ring.
  letI := e.commRing
  -- Local instance justification (proof-local temporary data): unpack its stored base algebra.
  letI := e.algebra
  -- Local instance justification (proof-local temporary data): unpack its stored square-zero projection.
  letI := e.isSquareZero
  let I : Ideal e.carrier := adicCompletionIdeal e J
  -- Local instance justification (proof-local temporary data): unpack square-zero evidence for the completed projection.
  letI := adicCompletion_projection_isSquareZero e J
  ∀ (r : AdicCompletion J B) x, adicCompletionKernelValue e J (r • x) =
    r • adicCompletionKernelValue e J x := sorry

omit [IsNoetherianRing B] [Module.Finite B N] in
/-- The two actions on the original cotangent have the same adic filtration:
`e.toB` is surjective and maps the inverse-image ideal onto `J`. -/
private theorem adicCompletion_cotangent_filtration_reverse
    (e : SquareZeroAlgExtension A B N) (J : Ideal B) :
  letI := e.commRing
  letI := e.algebra
  letI := e.isSquareZero
  let I : Ideal e.carrier := adicCompletionIdeal e J
  ∀ n (x : Ideal.Cotangent (RingHom.ker e.toB.toRingHom)),
    x ∈ (J ^ n • (⊤ : Submodule B (Ideal.Cotangent (RingHom.ker e.toB.toRingHom)))) →
    x ∈ (I ^ n • (⊤ : Submodule e.carrier (Ideal.Cotangent (RingHom.ker e.toB.toRingHom)))) := by
  letI := e.commRing
  letI := e.algebra
  letI := e.isSquareZero
  let I : Ideal e.carrier := adicCompletionIdeal e J
  change ∀ n (x : Ideal.Cotangent (RingHom.ker e.toB.toRingHom)),
    x ∈ (J ^ n • (⊤ : Submodule B (Ideal.Cotangent (RingHom.ker e.toB.toRingHom)))) →
    x ∈ (I ^ n • (⊤ : Submodule e.carrier (Ideal.Cotangent (RingHom.ker e.toB.toRingHom))))
  intro n x hx
  have hmap : Ideal.map e.toB.toRingHom (I ^ n) = J ^ n := by
    rw [Ideal.map_pow]
    congr 1
    exact Ideal.map_comap_of_surjective e.toB.toRingHom e.isSquareZero.surjective J
  refine Submodule.smul_induction_on hx ?_ ?_
  · intro r hr y _
    obtain ⟨a, ha, rfl⟩ := (Ideal.mem_map_iff_of_surjective e.toB.toRingHom
      e.isSquareZero.surjective).mp (hmap.symm ▸ hr)
    have hsmul : e.toB.toRingHom a • y = a • y := by
      change (e.toB.toRingHom.quotientKerEquivOfSurjective
        e.isSquareZero.surjective).symm (e.toB.toRingHom a) • y = a • y
      rw [RingHom.quotientKerEquivOfSurjective_symm_apply (f := e.toB.toRingHom)
        e.isSquareZero.surjective a]
      exact IsScalarTower.algebraMap_smul
        (e.carrier ⧸ RingHom.ker e.toB.toRingHom) a y
    rw [hsmul]
    exact Submodule.smul_mem_smul ha Submodule.mem_top
  · intro y z hy hz
    exact Submodule.add_mem _ hy hz

/-- The inverse kernel identification is induced by the original kernel inclusion;
it does not select a preimage using the bijectivity of the completed identification. -/
private def adicCompletionKernelInverse (e : SquareZeroAlgExtension A B N) (J : Ideal B) :
  letI := e.commRing
  letI := e.algebra
  letI := e.isSquareZero
  let I : Ideal e.carrier := adicCompletionIdeal e J
  letI := adicCompletion_projection_isSquareZero e J
  AdicCompletion J N → Ideal.Cotangent (RingHom.ker (adicCompletionProjection e J).toRingHom) :=
  letI := e.commRing
  letI := e.algebra
  letI := e.isSquareZero
  let I : Ideal e.carrier := adicCompletionIdeal e J
  letI := adicCompletion_projection_isSquareZero e J
  fun y ↦
    let yCot := AdicCompletion.map J e.kernelEquiv.symm.toLinearMap y
    let yCotI := FilteredAdditiveCompletion.map J I
      (AddMonoidHom.id (Ideal.Cotangent (RingHom.ker e.toB.toRingHom)))
      (adicCompletion_cotangent_filtration_reverse e J) yCot
    let yKer := AdicCompletion.map I
      (RingHom.SquareZeroExtension.toCotangentEquiv_source e.toB.toRingHom).symm.toLinearMap
      yCotI
    Ideal.toCotangent _ (adicCompletionKernelMap e J yKer)

private theorem adicCompletion_map_linearEquiv_symm
    {R M P : Type u} [CommRing R] [AddCommGroup M] [AddCommGroup P]
    [Module R M] [Module R P] (I : Ideal R) (f : M ≃ₗ[R] P)
    (x : AdicCompletion I M) :
    AdicCompletion.map I f.symm.toLinearMap (AdicCompletion.map I f.toLinearMap x) = x := by
  rw [AdicCompletion.map_comp_apply]
  have h : f.symm.toLinearMap.comp f.toLinearMap = LinearMap.id := by
    ext y
    exact f.symm_apply_apply y
  rw [h, AdicCompletion.map_id]
  rfl

private theorem adicCompletion_filtered_identity_inverse
    {R S M : Type u} [CommRing R] [CommRing S] [AddCommGroup M]
    [Module R M] [Module S M] (I : Ideal R) (J : Ideal S)
    (hIJ : ∀ n (x : M), x ∈ I ^ n • (⊤ : Submodule R M) →
      x ∈ J ^ n • (⊤ : Submodule S M))
    (hJI : ∀ n (x : M), x ∈ J ^ n • (⊤ : Submodule S M) →
      x ∈ I ^ n • (⊤ : Submodule R M)) (x : AdicCompletion I M) :
    FilteredAdditiveCompletion.map J I (AddMonoidHom.id M) hJI
      (FilteredAdditiveCompletion.map I J (AddMonoidHom.id M) hIJ x) = x := by
  apply Subtype.ext
  funext n
  change FilteredAdditiveCompletion.quotientMap J I (AddMonoidHom.id M) hJI n
    (FilteredAdditiveCompletion.quotientMap I J (AddMonoidHom.id M) hIJ n (x.val n)) = x.val n
  induction x.val n using Quotient.inductionOn' with
  | h y => rfl

/-- Completing the original kernel identification and inclusion gives mutually
inverse maps. These are properties of the explicit maps, not an existence claim
from which either map is selected. -/
private theorem adicCompletion_kernelValue_inverse (e : SquareZeroAlgExtension A B N)
    (J : Ideal B) :
  letI := e.commRing
  letI := e.algebra
  letI := e.isSquareZero
  let I : Ideal e.carrier := adicCompletionIdeal e J
  letI := adicCompletion_projection_isSquareZero e J
  Function.LeftInverse (adicCompletionKernelInverse e J) (adicCompletionKernelValue e J) ∧
    Function.RightInverse (adicCompletionKernelInverse e J) (adicCompletionKernelValue e J) := by
  letI := e.commRing
  letI := e.algebra
  letI := e.isSquareZero
  let I : Ideal e.carrier := adicCompletionIdeal e J
  letI := adicCompletion_projection_isSquareZero e J
  let E := RingHom.SquareZeroExtension.toCotangentEquiv_source
    (adicCompletionProjection e J).toRingHom
  let F := Equiv.ofBijective (adicCompletionKernelMap e J)
    (adicCompletion_kernelMap_bijective e J)
  let C := RingHom.SquareZeroExtension.toCotangentEquiv_source e.toB.toRingHom
  let t := AdicCompletion.map J e.kernelEquiv.toLinearMap
  let t' := AdicCompletion.map J e.kernelEquiv.symm.toLinearMap
  let s := FilteredAdditiveCompletion.map I J
    (AddMonoidHom.id (Ideal.Cotangent (RingHom.ker e.toB.toRingHom)))
    (adicCompletion_cotangent_filtration e J)
  let s' := FilteredAdditiveCompletion.map J I
    (AddMonoidHom.id (Ideal.Cotangent (RingHom.ker e.toB.toRingHom)))
    (adicCompletion_cotangent_filtration_reverse e J)
  let r := AdicCompletion.map I C.toLinearMap
  let r' := AdicCompletion.map I C.symm.toLinearMap
  have ht : Function.LeftInverse t' t := adicCompletion_map_linearEquiv_symm J e.kernelEquiv
  have ht' : Function.LeftInverse t t' := adicCompletion_map_linearEquiv_symm J e.kernelEquiv.symm
  have hs : Function.LeftInverse s' s := adicCompletion_filtered_identity_inverse I J
    (adicCompletion_cotangent_filtration e J) (adicCompletion_cotangent_filtration_reverse e J)
  have hs' : Function.LeftInverse s s' := adicCompletion_filtered_identity_inverse J I
    (adicCompletion_cotangent_filtration_reverse e J) (adicCompletion_cotangent_filtration e J)
  have hr : Function.LeftInverse r' r := adicCompletion_map_linearEquiv_symm I C
  have hr' : Function.LeftInverse r r' := adicCompletion_map_linearEquiv_symm I C.symm
  constructor
  · intro x
    change E (F (r' (s' (t' (t (s (r (F.symm (E.symm x))))))))) = x
    rw [ht, hs, hr, F.apply_symm_apply, E.apply_symm_apply]
  · intro y
    change t (s (r (F.symm (E.symm (E (F (r' (s' (t' y))))))))) = y
    rw [E.symm_apply_apply, F.symm_apply_apply, hr', hs', ht']

private theorem adicCompletion_kernelValue_bijective (e : SquareZeroAlgExtension A B N) (J : Ideal B) :
  -- Local instance justification (proof-local temporary data): unpack the stored middle ring.
  letI := e.commRing
  -- Local instance justification (proof-local temporary data): unpack its stored base algebra.
  letI := e.algebra
  -- Local instance justification (proof-local temporary data): unpack its stored square-zero projection.
  letI := e.isSquareZero
  let I : Ideal e.carrier := adicCompletionIdeal e J
  -- Local instance justification (proof-local temporary data): unpack square-zero evidence for the completed projection.
  letI := adicCompletion_projection_isSquareZero e J
  Function.Bijective (adicCompletionKernelValue e J) := by
  letI := e.commRing
  letI := e.algebra
  letI := e.isSquareZero
  letI := adicCompletion_projection_isSquareZero e J
  have h := adicCompletion_kernelValue_inverse e J
  exact ⟨h.1.injective, h.2.surjective⟩

/-- Complete the middle ring along the inverse image of an ideal, with its induced kernel identification. -/
def adicCompletion (e : SquareZeroAlgExtension A B N) (J : Ideal B) :
    SquareZeroAlgExtension A (AdicCompletion J B) (AdicCompletion J N) :=
  -- Local instance justification (proof-local temporary data): unpack the stored middle ring.
  letI := e.commRing
  -- Local instance justification (proof-local temporary data): unpack its stored base algebra.
  letI := e.algebra
  -- Local instance justification (proof-local temporary data): unpack its stored square-zero projection.
  letI := e.isSquareZero
  let I : Ideal e.carrier := adicCompletionIdeal e J
  let hpow (n : ℕ) : I ^ n ≤ (J ^ n).comap e.toB.toRingHom :=
    Ideal.map_le_iff_le_comap.mp (by
      rw [Ideal.map_pow]
      have hmap : Ideal.map e.toB.toRingHom I = J :=
        Ideal.map_comap_of_surjective e.toB.toRingHom e.isSquareZero.surjective J
      rw [hmap])
  let toB' : AdicCompletion I e.carrier →ₐ[A] AdicCompletion J B :=
    { toRingHom := AdicCompletion.liftRingHom J
        (fun n => (Ideal.quotientMap (J ^ n) e.toB.toRingHom (hpow n)).comp
          (AdicCompletion.evalₐ I n))
        (by
          intro m n h
          ext x
          induction x using AdicCompletion.induction_on I e.carrier with
          | _ a =>
            change Ideal.Quotient.mk (J ^ m) (e.toB (a n)) =
              Ideal.Quotient.mk (J ^ m) (e.toB (a m))
            apply Ideal.Quotient.eq.mpr
            rw [← map_sub]
            apply hpow m
            simpa only [smul_eq_mul, Ideal.mul_top] using SModEq.sub_mem.mp (a.property h).symm)
      commutes' := by exact adicCompletion_projection_commutes e J }
  -- Local instance justification (proof-local temporary data): the induced completed projection is square-zero.
  letI : toB'.toRingHom.IsSquareZeroExtension := by exact adicCompletion_projection_isSquareZero e J
  let completedKerIncl : AdicCompletion I (RingHom.ker e.toB.toRingHom) →
      RingHom.ker toB'.toRingHom :=
    fun z ↦ ⟨AdicCompletion.map I (Submodule.subtype (RingHom.ker e.toB.toRingHom)) z,
      by exact adicCompletion_kernelMap_mem e J z⟩
  let completedKerEquiv := Equiv.ofBijective completedKerIncl
    (by exact adicCompletion_kernelMap_bijective e J)
  of toB'
    { toFun := fun x ↦
        let xKer := (RingHom.SquareZeroExtension.toCotangentEquiv_source toB'.toRingHom).symm x
        let z := completedKerEquiv.symm xKer
        let zCot := AdicCompletion.map I (Ideal.toCotangent (RingHom.ker e.toB.toRingHom)) z
        let zCotJ := FilteredAdditiveCompletion.map I J
          (AddMonoidHom.id (Ideal.Cotangent (RingHom.ker e.toB.toRingHom)))
          (by exact adicCompletion_cotangent_filtration e J) zCot
        AdicCompletion.map J e.kernelEquiv.toLinearMap zCotJ
      map_add' := by exact adicCompletion_kernelValue_add e J
      map_smul' := by exact adicCompletion_kernelValue_smul e J
      invFun := fun y ↦
        let yCot := AdicCompletion.map J e.kernelEquiv.symm.toLinearMap y
        let yCotI := FilteredAdditiveCompletion.map J I
          (AddMonoidHom.id (Ideal.Cotangent (RingHom.ker e.toB.toRingHom)))
          (by exact adicCompletion_cotangent_filtration_reverse e J) yCot
        let yKer := AdicCompletion.map I
          (RingHom.SquareZeroExtension.toCotangentEquiv_source e.toB.toRingHom).symm.toLinearMap
          yCotI
        Ideal.toCotangent _ ⟨AdicCompletion.map I
          (Submodule.subtype (RingHom.ker e.toB.toRingHom)) yKer,
          by exact adicCompletion_kernelMap_mem e J yKer⟩
      left_inv := by exact (adicCompletion_kernelValue_inverse e J).1
      right_inv := by exact (adicCompletion_kernelValue_inverse e J).2 }

end Algebra.SquareZeroAlgExtension
namespace Algebra.Exal
variable (A B N : Type u) [CommRing A] [CommRing B] [Algebra A B]
variable [AddCommGroup N] [Module B N]

private theorem adicCompletion_respects [IsNoetherianRing B] [Module.Finite B N] (J : Ideal B)
    (f g : (Generators.self A B).toExtension.Cotangent →ₗ[B] N)
    (h : (LinearMap.range
      (LinearMap.lcomp B N (Generators.self A B).toExtension.cotangentComplex)).quotientRel f g) :
    SquareZeroAlgExtension.toClass ((SquareZeroAlgExtension.ofHom f).adicCompletion J) =
      SquareZeroAlgExtension.toClass ((SquareZeroAlgExtension.ofHom g).adicCompletion J) := sorry

/-- Completion of geometric extensions descends to their cotangent cokernel classes. -/
def adicCompletion [IsNoetherianRing B] [Module.Finite B N] (J : Ideal B) :
    Exal A B N → Exal A (AdicCompletion J B) (AdicCompletion J N) :=
  fun x ↦ Quotient.liftOn x
    (fun f ↦ SquareZeroAlgExtension.toClass ((SquareZeroAlgExtension.ofHom f).adicCompletion J))
    (by exact adicCompletion_respects A B N J)

/-- Completing a conormal class gives the class of its completed graph-ideal realization. -/
theorem adicCompletion_mk [IsNoetherianRing B] [Module.Finite B N] (J : Ideal B)
    (f : (Generators.self A B).toExtension.Cotangent →ₗ[B] N) :
    adicCompletion A B N J (mk A B N f) =
      SquareZeroAlgExtension.toClass ((SquareZeroAlgExtension.ofHom f).adicCompletion J) := rfl

/-- Quotient representatives and named conormal classes have the same completion. -/
theorem adicCompletion_apply [IsNoetherianRing B] [Module.Finite B N] (J : Ideal B)
    (f : (Generators.self A B).toExtension.Cotangent →ₗ[B] N) :
    adicCompletion A B N J (Quotient.mk _ f) = adicCompletion A B N J (mk A B N f) := rfl

/-- The completion of the class of any geometric extension is the class of its completion. -/
theorem adicCompletion_toClass [IsNoetherianRing B] [Module.Finite B N] (J : Ideal B)
    (e : SquareZeroAlgExtension A B N) :
    adicCompletion A B N J e.toClass = (e.adicCompletion J).toClass := sorry

end Algebra.Exal
namespace Algebra.Exal
variable (k B N : Type u) [Field k] [CommRing B] [Algebra k B]
variable [AddCommGroup N] [Module B N]

/-- Completion of extension classes for a finite type algebra over a field. -/
def adicCompletionOfFiniteType [Algebra.FiniteType k B] [Module.Finite B N] (J : Ideal B) :
    Exal k B N → Exal k (AdicCompletion J B) (AdicCompletion J N) :=
  -- Local instance justification (proof-local temporary data): the base field supplies Noetherianity, but is not determined by B.
  letI := Algebra.FiniteType.isNoetherianRing k B
  adicCompletion k B N J

/-- For a finite type algebra over a field, smooth outside the closed subset of an ideal,
completion induces a bijection on square-zero extension classes with finite coefficients. -/
theorem adicCompletion_bijective [Algebra.FiniteType k B] [Module.Finite B N]
    (J : Ideal B) (hsmooth : (PrimeSpectrum.zeroLocus (J : Set B))ᶜ ⊆ smoothLocus k B) :
    Function.Bijective (adicCompletionOfFiniteType k B N J) := sorry

end Algebra.Exal
