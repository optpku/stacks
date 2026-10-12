/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import Mathlib.RingTheory.Spectrum.Prime.RingHom
public import Mathlib.RingTheory.TensorProduct.Maps
public import Mathlib.Tactic.CrossRefAttribute
public import ReasLib.RingTheory.Algebra.TensorProduct.Flat
public import ReasLib.RingTheory.KrullDimension.Fiber
public import ReasLib.RingTheory.KrullDimension.GoingDown

@[expose] public section

/-!
# Fibers of Surjective Tensor Base Change

This leaf packages the order-theoretic comparison of prime-spectrum fibers
induced by tensoring a surjective algebra map on the left.  The construction
is independent of a chosen polynomial presentation.
-/

universe u v w x

open scoped TensorProduct Algebra.TensorProduct.Right

namespace Algebra.TensorProduct

variable {R : Type u} {T : Type v} {A : Type w} {B : Type x}
variable [CommRing R] [CommRing T] [CommRing A] [CommRing B]
variable [Algebra R T] [Algebra R A] [Algebra R B]

/-- A surjective `R`-algebra map identifies the raw fiber over its contracted target prime after
left tensor base change with the raw fiber over that target prime. -/
@[stacks 00P4 "surjective tensor base-change raw-fiber support"]
noncomputable def preimageFiberOrderIso_of_surjective
    (f : A →ₐ[R] B) (hf : Function.Surjective f) (p : PrimeSpectrum B) :
    (PrimeSpectrum.comap
        (Algebra.TensorProduct.includeRight : A →ₐ[R] T ⊗[R] A).toRingHom) ⁻¹'
        {PrimeSpectrum.comap f.toRingHom p} ≃o
      (PrimeSpectrum.comap
        (Algebra.TensorProduct.includeRight : B →ₐ[R] T ⊗[R] B).toRingHom) ⁻¹' {p} := by
  let fT : T ⊗[R] A →+* T ⊗[R] B :=
    (Algebra.TensorProduct.map (AlgHom.id R T) f).toRingHom
  have hfT : Function.Surjective fT := by
    intro y
    obtain ⟨x, hx⟩ :=
      Algebra.TensorProduct.map_surjective (AlgHom.id R T) f Function.surjective_id hf y
    refine ⟨x, ?_⟩
    change Algebra.TensorProduct.map (AlgHom.id R T) f x = y
    exact hx
  have hker : RingHom.ker fT =
      (RingHom.ker f).map
        (Algebra.TensorProduct.includeRight : A →ₐ[R] T ⊗[R] A) := by
    change RingHom.ker ((Algebra.TensorProduct.map (AlgHom.id R T) f).toRingHom) =
      (RingHom.ker f).map
        (Algebra.TensorProduct.includeRight : A →ₐ[R] T ⊗[R] A)
    rw [AlgHom.toRingHom_eq_coe, RingHom.ker_coe_toRingHom]
    exact Algebra.TensorProduct.lTensor_ker (A := T) (g := f) hf
  have hmap :
      fT.comp (Algebra.TensorProduct.includeRight : A →ₐ[R] T ⊗[R] A).toRingHom =
        (Algebra.TensorProduct.includeRight : B →ₐ[R] T ⊗[R] B).toRingHom.comp f.toRingHom := by
    ext a
    simp [fT]
  let eQuot := Ideal.primeSpectrumOrderIsoZeroLocusOfSurj fT hfT hker
  have hQuot_val (q : PrimeSpectrum (T ⊗[R] B)) :
      (eQuot q).1 = PrimeSpectrum.comap fT q := rfl
  have hcomap (q : PrimeSpectrum (T ⊗[R] B)) :
      PrimeSpectrum.comap f.toRingHom
          (PrimeSpectrum.comap
            (Algebra.TensorProduct.includeRight : B →ₐ[R] T ⊗[R] B).toRingHom q) =
        PrimeSpectrum.comap
          (Algebra.TensorProduct.includeRight : A →ₐ[R] T ⊗[R] A).toRingHom
          (PrimeSpectrum.comap fT q) := by
    rw [← PrimeSpectrum.comap_comp_apply, ← PrimeSpectrum.comap_comp_apply]
    exact congrArg (fun g ↦ PrimeSpectrum.comap g q) hmap.symm
  let toFun :
      ((PrimeSpectrum.comap
          (Algebra.TensorProduct.includeRight : A →ₐ[R] T ⊗[R] A).toRingHom) ⁻¹'
          {PrimeSpectrum.comap f.toRingHom p}) →
        ((PrimeSpectrum.comap
          (Algebra.TensorProduct.includeRight : B →ₐ[R] T ⊗[R] B).toRingHom) ⁻¹' {p}) :=
    fun rOver ↦ by
      have hker_p : RingHom.ker f ≤ (PrimeSpectrum.comap f.toRingHom p).asIdeal := by
        intro a ha
        change f a ∈ p.asIdeal
        rw [RingHom.mem_ker.mp ha]
        exact p.asIdeal.zero_mem
      have hker_r : RingHom.ker fT ≤ rOver.1.asIdeal := by
        rw [hker, Ideal.map_le_iff_le_comap]
        have hr : (PrimeSpectrum.comap f.toRingHom p).asIdeal =
            Ideal.comap
              (Algebra.TensorProduct.includeRight : A →ₐ[R] T ⊗[R] A).toRingHom
              rOver.1.asIdeal := by
          simpa [PrimeSpectrum.comap_asIdeal] using
            (congrArg PrimeSpectrum.asIdeal rOver.2).symm
        exact hker_p.trans hr.le
      have hzero_r :
          (RingHom.ker f).map
              (Algebra.TensorProduct.includeRight : A →ₐ[R] T ⊗[R] A) ≤ rOver.1.asIdeal := by
        rwa [← hker]
      let q : PrimeSpectrum (T ⊗[R] B) :=
        eQuot.symm ⟨rOver.1, (PrimeSpectrum.mem_zeroLocus rOver.1 _).2 hzero_r⟩
      refine ⟨q, ?_⟩
      have hfTq : PrimeSpectrum.comap fT q = rOver.1 :=
        congrArg Subtype.val
          (eQuot.right_inv ⟨rOver.1, (PrimeSpectrum.mem_zeroLocus rOver.1 _).2 hzero_r⟩)
      apply PrimeSpectrum.comap_injective_of_surjective f.toRingHom hf
      calc
        PrimeSpectrum.comap f.toRingHom
            (PrimeSpectrum.comap
              (Algebra.TensorProduct.includeRight : B →ₐ[R] T ⊗[R] B).toRingHom q) =
            PrimeSpectrum.comap
              (Algebra.TensorProduct.includeRight : A →ₐ[R] T ⊗[R] A).toRingHom
              (PrimeSpectrum.comap fT q) := hcomap q
        _ = PrimeSpectrum.comap
              (Algebra.TensorProduct.includeRight : A →ₐ[R] T ⊗[R] A).toRingHom rOver.1 := by
              rw [hfTq]
        _ = PrimeSpectrum.comap f.toRingHom p := rOver.2
  let invFun :
      ((PrimeSpectrum.comap
          (Algebra.TensorProduct.includeRight : B →ₐ[R] T ⊗[R] B).toRingHom) ⁻¹' {p}) →
        ((PrimeSpectrum.comap
          (Algebra.TensorProduct.includeRight : A →ₐ[R] T ⊗[R] A).toRingHom) ⁻¹'
          {PrimeSpectrum.comap f.toRingHom p}) :=
    fun qOver ↦ ⟨PrimeSpectrum.comap fT qOver.1, by
      calc
        PrimeSpectrum.comap
            (Algebra.TensorProduct.includeRight : A →ₐ[R] T ⊗[R] A).toRingHom
            (PrimeSpectrum.comap fT qOver.1) =
            PrimeSpectrum.comap f.toRingHom
              (PrimeSpectrum.comap
                (Algebra.TensorProduct.includeRight : B →ₐ[R] T ⊗[R] B).toRingHom qOver.1) :=
              (hcomap qOver.1).symm
        _ = PrimeSpectrum.comap f.toRingHom p := by rw [qOver.2]⟩
  have hfT_toFun
      (rOver :
        ((PrimeSpectrum.comap
            (Algebra.TensorProduct.includeRight : A →ₐ[R] T ⊗[R] A).toRingHom) ⁻¹'
            {PrimeSpectrum.comap f.toRingHom p})) :
      PrimeSpectrum.comap fT (toFun rOver).1 = rOver.1 := by
    dsimp [toFun]
    have hker_p : RingHom.ker f ≤ (PrimeSpectrum.comap f.toRingHom p).asIdeal := by
      intro a ha
      change f a ∈ p.asIdeal
      rw [RingHom.mem_ker.mp ha]
      exact p.asIdeal.zero_mem
    have hker_r : RingHom.ker fT ≤ rOver.1.asIdeal := by
      rw [hker, Ideal.map_le_iff_le_comap]
      have hr : (PrimeSpectrum.comap f.toRingHom p).asIdeal =
          Ideal.comap
            (Algebra.TensorProduct.includeRight : A →ₐ[R] T ⊗[R] A).toRingHom
            rOver.1.asIdeal := by
        simpa [PrimeSpectrum.comap_asIdeal] using
          (congrArg PrimeSpectrum.asIdeal rOver.2).symm
      exact hker_p.trans hr.le
    have hzero_r :
        (RingHom.ker f).map
            (Algebra.TensorProduct.includeRight : A →ₐ[R] T ⊗[R] A) ≤ rOver.1.asIdeal := by
      rwa [← hker]
    exact congrArg Subtype.val
      (eQuot.right_inv ⟨rOver.1, (PrimeSpectrum.mem_zeroLocus rOver.1 _).2 hzero_r⟩)
  exact
    { toEquiv :=
        { toFun := toFun
          invFun := invFun
          left_inv := by
            intro rOver
            apply Subtype.ext
            exact hfT_toFun rOver
          right_inv := by
            intro qOver
            apply Subtype.ext
            apply PrimeSpectrum.comap_injective_of_surjective fT hfT
            rw [hfT_toFun (invFun qOver)] }
      map_rel_iff' := by
        intro a b
        constructor
        · intro h
          have h' : eQuot (toFun a).1 ≤ eQuot (toFun b).1 :=
            (eQuot.map_rel_iff').2 h
          change a.1 ≤ b.1
          change (eQuot (toFun a).1).1 ≤ (eQuot (toFun b).1).1 at h'
          rw [hQuot_val (toFun a).1, hQuot_val (toFun b).1,
            hfT_toFun a, hfT_toFun b] at h'
          exact h'
        · intro h
          have h' : eQuot (toFun a).1 ≤ eQuot (toFun b).1 := by
            change (eQuot (toFun a).1).1 ≤ (eQuot (toFun b).1).1
            rw [hQuot_val (toFun a).1, hQuot_val (toFun b).1,
              hfT_toFun a, hfT_toFun b]
            exact h
          exact (eQuot.map_rel_iff').1 h' }

/-- A surjective `R`-algebra map induces an order isomorphism from the raw fiber over a target
prime after left tensor base change to the corresponding preimage raw fiber.  Its forward map is
the canonical contraction along the tensor base-change map. -/
@[stacks 00P4 "surjective tensor base-change raw-fiber support"]
noncomputable def comapFiberOrderIso_of_surjective
    (f : A →ₐ[R] B) (hf : Function.Surjective f) (p : PrimeSpectrum B) :
    (PrimeSpectrum.comap
        (Algebra.TensorProduct.includeRight : B →ₐ[R] T ⊗[R] B).toRingHom) ⁻¹' {p} ≃o
      (PrimeSpectrum.comap
        (Algebra.TensorProduct.includeRight : A →ₐ[R] T ⊗[R] A).toRingHom) ⁻¹'
        {PrimeSpectrum.comap f.toRingHom p} :=
  (preimageFiberOrderIso_of_surjective (T := T) f hf p).symm

/-- The forward map of `comapFiberOrderIso_of_surjective` is contraction along the tensor
base-change map. -/
@[simp, stacks 00P4 "surjective tensor base-change raw-fiber support"]
theorem comapFiberOrderIso_of_surjective_apply
    (f : A →ₐ[R] B) (hf : Function.Surjective f) (p : PrimeSpectrum B)
    (q : (PrimeSpectrum.comap
      (Algebra.TensorProduct.includeRight : B →ₐ[R] T ⊗[R] B).toRingHom) ⁻¹' {p}) :
    (comapFiberOrderIso_of_surjective (T := T) f hf p q).1 =
      PrimeSpectrum.comap
        (Algebra.TensorProduct.map (AlgHom.id R T) f).toRingHom q.1 := sorry

/-- Under a surjective algebra map, corresponding fiber primes after left tensor base change have
the same order height. -/
@[stacks 00P4 "surjective tensor base-change fiber-prime support"]
theorem fiberPrimeAt_orderHeight_eq_of_surjective
    (f : A →ₐ[R] B) (hf : Function.Surjective f)
    (q : PrimeSpectrum (T ⊗[R] B)) :
    Order.height
        (fiberPrimeAt A (T ⊗[R] A)
          (PrimeSpectrum.comap
            (Algebra.TensorProduct.map (AlgHom.id R T) f).toRingHom q)) =
      Order.height (fiberPrimeAt B (T ⊗[R] B) q) := sorry

/-- Under a surjective algebra map, flat left tensor base change preserves the prime height
defect of the presentation at corresponding points. -/
@[stacks 00P4 "surjective tensor base-change prime height-defect support"]
theorem primeHeightDefect_baseChange_eq_of_surjective
    [Module.Flat R T]
    [IsNoetherianRing A] [IsNoetherianRing B]
    [IsNoetherianRing (T ⊗[R] A)] [IsNoetherianRing (T ⊗[R] B)]
    (f : A →ₐ[R] B) (hf : Function.Surjective f)
    (q : PrimeSpectrum (T ⊗[R] B)) :
    RingHom.primeHeightDefect
        (Algebra.TensorProduct.map (AlgHom.id R T) f).toRingHom q =
      RingHom.primeHeightDefect f.toRingHom
        (PrimeSpectrum.comap
          (Algebra.TensorProduct.includeRight : B →ₐ[R] T ⊗[R] B).toRingHom q) := sorry

end Algebra.TensorProduct
