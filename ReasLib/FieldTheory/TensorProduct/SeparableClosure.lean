/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import Mathlib.FieldTheory.Galois.Infinite
public import Mathlib.FieldTheory.Galois.Profinite
public import Mathlib.FieldTheory.IsSepClosed
public import Mathlib.LinearAlgebra.TensorProduct.Basis
public import Mathlib.RingTheory.Invariant.Profinite
public import Mathlib.Tactic.CrossRefAttribute
public import ReasLib.FieldTheory.TensorProduct.Galois
public import ReasLib.RingTheory.Algebra.TensorProduct.RightAlgebra

/-!
# Galois Actions After Separable Closure

This leaf specializes the neutral left tensor-factor action to a separable
closure.  The action itself is canonical and globally available.  The right
scalar structure and discrete topology are intentionally scoped: they are the
choices needed by the profinite invariant-extension theorem, but are not the
only structures a tensor product may reasonably carry.
-/

@[expose] public section

open scoped TensorProduct

universe u v

namespace Algebra.TensorProduct.SeparableClosure.Galois

open scoped Algebra.TensorProduct.Right
open scoped Pointwise

variable {k : Type u} {K : Type v}
variable [Field k] [Field K] [Algebra k K]

namespace Action

/-- The canonical action of `Gal(SeparableClosure k/k)` on
`SeparableClosure k ⊗[k] K`, acting on the left tensor factor. -/
@[stacks 04KP "canonical tensor action"]
noncomputable instance ring :
    MulSemiringAction (Gal(SeparableClosure k/k))
      (SeparableClosure k ⊗[k] K) :=
  Algebra.TensorProduct.Galois.leftAction
    (k := k) (L := SeparableClosure k) (K := K)

/-- The canonical action of `Gal(SeparableClosure k/k)` on primes of
`SeparableClosure k ⊗[k] K`. -/
@[stacks 04KP "canonical prime-spectrum action"]
noncomputable instance primes :
    MulAction (Gal(SeparableClosure k/k))
      (PrimeSpectrum (SeparableClosure k ⊗[k] K)) :=
  Algebra.TensorProduct.Galois.primeAction
    (k := k) (L := SeparableClosure k) (K := K)

end Action

private theorem smul_tmul (σ : Gal(SeparableClosure k/k))
    (x : SeparableClosure k) (y : K) :
    σ • (x ⊗ₜ[k] y) = σ x ⊗ₜ[k] y := by
  change Algebra.TensorProduct.congr σ (AlgEquiv.refl : K ≃ₐ[k] K) (x ⊗ₜ[k] y) = _
  simp

/- Re-export the neutral right tensor-factor algebra through the separable-closure scope, so the
specialized continuous-action support is enabled by one scoped import. -/
attribute [scoped instance]
  Algebra.TensorProduct.rightAlgebra

/-- The discrete topology used on `SeparableClosure k ⊗[k] K` by the profinite
invariant-extension argument.  Enable it with
`open scoped Algebra.TensorProduct.SeparableClosure.Galois`. -/
noncomputable scoped instance topology :
    TopologicalSpace (SeparableClosure k ⊗[k] K) :=
  ⊥

/-- The scoped tensor-product topology is discrete. -/
scoped instance discrete : DiscreteTopology (SeparableClosure k ⊗[k] K) := ⟨rfl⟩

/-- The left Galois action commutes with the scoped right `K`-scalar action. -/
scoped instance commutes :
    SMulCommClass (Gal(SeparableClosure k/k)) K
      (SeparableClosure k ⊗[k] K) := by
  constructor
  intro σ a z
  induction z using TensorProduct.induction_on with
  | zero => simp [Algebra.smul_def]
  | tmul x y =>
      simp [Algebra.smul_def, smul_tmul,
        right_algebraMap_apply, TensorProduct.tmul_mul_tmul]
  | add x y hx hy =>
      calc
        σ • (a • (x + y)) = σ • (a • x + a • y) := congrArg (σ • ·) (smul_add a x y)
        _ = σ • (a • x) + σ • (a • y) := smul_add σ _ _
        _ = a • (σ • x) + a • (σ • y) := congrArg₂ (· + ·) hx hy
        _ = a • (σ • x + σ • y) := (smul_add a _ _).symm
        _ = a • (σ • (x + y)) := congrArg (a • ·) (smul_add σ x y).symm

/-- The left Galois action is continuous for the Krull topology on the Galois
group and the scoped discrete topology on the tensor product. -/
@[stacks 04KP "continuous tensor action"]
scoped instance continuous :
    ContinuousSMul (Gal(SeparableClosure k/k))
      (SeparableClosure k ⊗[k] K) := by
  apply continuousSMul_iff_stabilizer_isOpen.mpr
  intro z
  induction z using TensorProduct.induction_on with
  | zero =>
      change IsOpen {σ : Gal(SeparableClosure k/k) |
        σ • (0 : SeparableClosure k ⊗[k] K) = 0}
      simpa using (isOpen_univ : IsOpen (Set.univ : Set Gal(SeparableClosure k/k)))
  | tmul x y =>
      refine Subgroup.isOpen_mono (H₁ := MulAction.stabilizer (Gal(SeparableClosure k/k)) x)
        ?_ (stabilizer_isOpen_of_isIntegral x)
      intro σ hσ
      change σ • (x ⊗ₜ[k] y) = x ⊗ₜ[k] y
      rw [smul_tmul, show σ x = x from hσ]
  | add x y hx hy =>
      refine Subgroup.isOpen_mono
        (H₁ := MulAction.stabilizer (Gal(SeparableClosure k/k)) x ⊓
          MulAction.stabilizer (Gal(SeparableClosure k/k)) y) ?_ (hx.inter hy)
      intro σ hσ
      change σ • (x + y) = x + y
      rw [smul_add, show σ • x = x from hσ.1, show σ • y = y from hσ.2]

/-- Every fixed point of the left Galois action lies in the scoped right copy
of `K` in `SeparableClosure k ⊗[k] K`.  Together with `commutes`, this gives
the usual fixed-point identification. -/
@[stacks 04KP "invariant tensor extension"]
scoped instance invariant :
    Algebra.IsInvariant K (SeparableClosure k ⊗[k] K)
      (Gal(SeparableClosure k/k)) where
  isInvariant z hz := by
    classical
    let b := Module.Basis.ofVectorSpace k K
    let e := b.baseChange (SeparableClosure k)
    -- In a right-factor basis, the action applies to each left-factor coefficient.
    have hcoord (σ : Gal(SeparableClosure k/k)) (w : SeparableClosure k ⊗[k] K) (i) :
        e.repr (σ • w) i = σ (e.repr w i) := by
      induction w using TensorProduct.induction_on with
      | zero => simp
      | tmul x y => simp [e, smul_tmul, Algebra.smul_def]
      | add x y hx hy => simp [hx, hy]
    have hf (i) : ∃ a : k, algebraMap k (SeparableClosure k) a = e.repr z i := by
      apply (InfiniteGalois.mem_range_algebraMap_iff_fixed _).mpr
      intro σ
      have hzσ := hz σ
      exact (hcoord σ z i).symm.trans (congrArg (fun w => e.repr w i) hzσ)
    choose c hc using hf
    refine ⟨(e.repr z).support.sum (fun i => c i • b i), ?_⟩
    calc
      algebraMap K (SeparableClosure k ⊗[k] K)
          ((e.repr z).support.sum (fun i => c i • b i)) =
          (e.repr z).support.sum (fun i => algebraMap k (SeparableClosure k) (c i) ⊗ₜ[k] b i) := by
        rw [map_sum]
        apply Finset.sum_congr rfl
        intro i hi
        change (Algebra.ofId K (SeparableClosure k ⊗[k] K)) (c i • b i) = _
        rw [(Algebra.ofId K (SeparableClosure k ⊗[k] K)).map_smul_of_tower]
        simp [right_algebraMap_apply, Algebra.smul_def]
      _ = (e.repr z).support.sum (fun i => e.repr z i • e i) := by
        apply Finset.sum_congr rfl
        intro i hi
        rw [hc, Module.Basis.baseChange_apply, TensorProduct.smul_tmul', smul_eq_mul, mul_one]
      _ = z := by
        simpa only [Finsupp.linearCombination_apply, Finsupp.sum] using e.linearCombination_repr z

/-- The canonical prime-spectrum action is pullback along the inverse of the
left tensor-factor automorphism. -/
@[stacks 04KP "prime action formula"]
theorem smul_def (σ : Gal(SeparableClosure k/k))
    (p : PrimeSpectrum (SeparableClosure k ⊗[k] K)) :
    σ • p =
      Algebra.TensorProduct.Galois.primeMap
        (k := k) (L := SeparableClosure k) (K := K) σ p := rfl

/-- On prime ideals, the spectrum action is the image under the corresponding
left tensor-factor automorphism. -/
@[stacks 04KP "ideal action formula"]
theorem prime_smul (σ : Gal(SeparableClosure k/k))
    (p : PrimeSpectrum (SeparableClosure k ⊗[k] K)) :
    (σ • p).asIdeal =
      Ideal.map
        ((Algebra.TensorProduct.Galois.leftAut
          (k := k) (L := SeparableClosure k) (K := K) σ).toRingEquiv)
        p.asIdeal := by
  exact Ideal.comap_symm
    ((Algebra.TensorProduct.Galois.leftAut
      (k := k) (L := SeparableClosure k) (K := K) σ).toRingEquiv)

/-- Lemma 10.47.14 (Tag 04KP): the canonical pretransitivity instance for the
Galois action on primes of `SeparableClosure k ⊗[k] K`. -/
@[stacks 04KP]
instance pretransitive :
    MulAction.IsPretransitive (Gal(SeparableClosure k/k))
      (PrimeSpectrum (SeparableClosure k ⊗[k] K)) where
  exists_smul_eq p q := by
    have hpprime : (p.asIdeal.under K).IsPrime := by infer_instance
    have hqprime : (q.asIdeal.under K).IsPrime := by infer_instance
    have hp : p.asIdeal.under K = (⊥ : Ideal K) := by
      exact (IsSimpleOrder.eq_bot_or_eq_top _).resolve_right hpprime.ne_top'
    have hq : q.asIdeal.under K = (⊥ : Ideal K) := by
      exact (IsSimpleOrder.eq_bot_or_eq_top _).resolve_right hqprime.ne_top'
    -- Supply the scoped right algebra and its action support explicitly.
    obtain ⟨σ, hσ⟩ := @Algebra.IsInvariant.exists_smul_of_under_eq_of_profinite
      K (SeparableClosure k ⊗[k] K) _ _ Algebra.TensorProduct.rightAlgebra
      (Gal(SeparableClosure k/k)) _ Action.ring commutes _ _ _ _ topology discrete
      continuous invariant p.asIdeal q.asIdeal _ _ (hp.trans hq.symm)
    refine ⟨σ, PrimeSpectrum.ext ?_⟩
    rw [prime_smul]
    exact hσ.symm

/-- Lemma 10.47.14 (Tag 04KP), elementwise form: any two primes of
`SeparableClosure k ⊗[k] K` are conjugate under the canonical Galois action. -/
@[stacks 04KP "elementwise form"]
theorem exists_smul_eq (p q : PrimeSpectrum (SeparableClosure k ⊗[k] K)) :
    ∃ σ : Gal(SeparableClosure k/k), σ • p = q :=
  MulAction.exists_smul_eq (Gal(SeparableClosure k/k)) p q

end Algebra.TensorProduct.SeparableClosure.Galois

section

open scoped Algebra.TensorProduct.SeparableClosure.Galois

variable {k : Type u} {K : Type v}
variable [Field k] [Field K] [Algebra k K]

#synth Algebra K (SeparableClosure k ⊗[k] K)
#synth DiscreteTopology (SeparableClosure k ⊗[k] K)
#synth SMulCommClass (Gal(SeparableClosure k/k)) K (SeparableClosure k ⊗[k] K)
#synth ContinuousSMul (Gal(SeparableClosure k/k)) (SeparableClosure k ⊗[k] K)
#synth Algebra.IsInvariant K (SeparableClosure k ⊗[k] K) (Gal(SeparableClosure k/k))

end
