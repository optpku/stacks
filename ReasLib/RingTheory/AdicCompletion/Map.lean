/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import Mathlib.RingTheory.AdicCompletion.RingHom
public import Mathlib.Tactic.CrossRefAttribute
public import ReasLib.RingTheory.Topology.Adic.Continuity

@[expose] public section

/-!
# Maps induced on adic completions

This file owns the finite quotient maps and the map on completions induced by
an adically continuous ring homomorphism.  It is independent of smoothness
hypotheses and of ambient topology instances.

@stack 07ED
-/

open scoped Topology

noncomputable section

universe u v w

namespace RingHom

variable {R : Type u} {S : Type v} [CommRing R] [CommRing S]

open AdicCompletion Ideal.Quotient

namespace AdicContinuous

/-- The power bound used to construct finite quotients, proved directly from
an actual continuity witness rather than an admitted existence lemma. -/
theorem pow_le_comap
    {I : Ideal R} {J : Ideal S} {f : R →+* S}
    (h : f.AdicContinuous I J) (n : ℕ) :
    I ^ (h.exponent * n) ≤ (J ^ n).comap f := by
  apply Ideal.map_le_iff_le_comap.mp
  rw [pow_mul, Ideal.map_pow]
  exact Ideal.pow_right_mono (Classical.choose_spec h) n

/-- The finite quotient map induced by an adically continuous ring
homomorphism. -/
noncomputable def quotientMap
    {I : Ideal R} {J : Ideal S} {f : R →+* S}
    (h : f.AdicContinuous I J) (n : ℕ) :
    AdicCompletion I R →+* S ⧸ J ^ n :=
  (Ideal.quotientMap (J ^ n) f
      (pow_le_comap h n)).comp
    (evalₐ I (h.exponent * n))

/-- The finite quotient map extends the original ring homomorphism modulo
the prescribed target power. -/
theorem quotientMap_comp
    {I : Ideal R} {J : Ideal S} {f : R →+* S}
    (h : f.AdicContinuous I J) (n : ℕ) :
    (h.quotientMap n).comp (algebraMap R (AdicCompletion I R)) =
      (Ideal.Quotient.mk (J ^ n)).comp f := by
  ext r
  simp [quotientMap, AdicCompletion.algebraMap_apply]

/-- The finite quotient maps induced by adic continuity commute with the
transition maps. -/
theorem quotientMap_compatible
    {I : Ideal R} {J : Ideal S} {f : R →+* S}
    (h : f.AdicContinuous I J) {m n : ℕ} (hle : m ≤ n) :
    (factorPow J hle).comp (h.quotientMap n) = h.quotientMap m := by
  apply RingHom.ext
  intro x
  induction x using AdicCompletion.induction_on with
  | _ a =>
    change factorPow J hle (Ideal.quotientMap (J ^ n) f (pow_le_comap h n)
        (evalₐ I (h.exponent * n) (AdicCompletion.mk I R a))) =
      Ideal.quotientMap (J ^ m) f (pow_le_comap h m)
        (evalₐ I (h.exponent * m) (AdicCompletion.mk I R a))
    simp only [AdicCompletion.evalₐ_mk, Ideal.quotientMap_mk]
    change Ideal.Quotient.mk (J ^ m) (f (a.val (h.exponent * n))) =
      Ideal.Quotient.mk (J ^ m) (f (a.val (h.exponent * m)))
    apply Ideal.Quotient.eq.mpr
    rw [← map_sub]
    apply pow_le_comap h m
    simpa only [smul_eq_mul, Ideal.mul_top] using
      SModEq.sub_mem.mp (a.property (Nat.mul_le_mul_left h.exponent hle)).symm

/-- The canonical morphism between adic completions induced by an adically
continuous ring homomorphism. -/
@[stacks 07ED "completion map of an adically continuous ring homomorphism"]
noncomputable def completionMap
    {I : Ideal R} {J : Ideal S} {f : R →+* S}
    (h : f.AdicContinuous I J) :
    AdicCompletion I R →+* AdicCompletion J S :=
  liftRingHom J h.quotientMap h.quotientMap_compatible

/-- Evaluating the induced completion map at a finite quotient recovers its
defining quotient map. -/
theorem eval_completionMap
    {I : Ideal R} {J : Ideal S} {f : R →+* S}
    (h : f.AdicContinuous I J) (n : ℕ) :
    (evalₐ J n).toRingHom.comp h.completionMap = h.quotientMap n :=
  AdicCompletion.evalₐ_comp_liftRingHom J _ _ n

/-- The completion map induced by adic continuity extends the original ring
homomorphism. -/
theorem completionMap_comp
    {I : Ideal R} {J : Ideal S} {f : R →+* S}
    (h : f.AdicContinuous I J) :
    h.completionMap.comp (algebraMap R (AdicCompletion I R)) =
      (algebraMap S (AdicCompletion J S)).comp f := by
  apply RingHom.ext
  intro r
  apply AdicCompletion.ext_evalₐ
  intro n
  have h₁ := RingHom.congr_fun (h.eval_completionMap n)
    (algebraMap R (AdicCompletion I R) r)
  have h₂ := RingHom.congr_fun (h.quotientMap_comp n) r
  exact h₁.trans (h₂.trans (by simp [AdicCompletion.algebraMap_apply]))

/-- Any finite source level whose ideal maps into the target power computes
that finite component of the completion map. In particular the construction
is independent of the chosen continuity exponent. -/
theorem quotientMap_eq_of_pow_le
    {I : Ideal R} {J : Ideal S} {f : R →+* S}
    (h : f.AdicContinuous I J) (n m : ℕ) (hm : I ^ m ≤ (J ^ n).comap f) :
    h.quotientMap n =
      (Ideal.quotientMap (J ^ n) f hm).comp (evalₐ I m).toRingHom := by
  ext x
  induction x using AdicCompletion.induction_on with
  | _ a =>
    change Ideal.quotientMap (J ^ n) f (pow_le_comap h n)
        (evalₐ I (h.exponent * n) (AdicCompletion.mk I R a)) =
      Ideal.quotientMap (J ^ n) f hm (evalₐ I m (AdicCompletion.mk I R a))
    simp only [AdicCompletion.evalₐ_mk, Ideal.quotientMap_mk]
    apply Ideal.Quotient.eq.mpr
    rw [← map_sub]
    rcases le_total (h.exponent * n) m with hle | hle
    · apply pow_le_comap h n
      simpa only [smul_eq_mul, Ideal.mul_top] using SModEq.sub_mem.mp (a.property hle)
    · apply hm
      simpa only [smul_eq_mul, Ideal.mul_top] using
        SModEq.sub_mem.mp (a.property hle).symm

/-- The algebra homomorphism on completions induced by a continuous algebra
homomorphism. The underlying ring map is the shared completion construction. -/
noncomputable def completionAlgHom
    {T : Type w} [CommRing T] [Algebra T R] [Algebra T S]
    (I : Ideal R) (J : Ideal S) (f : R →ₐ[T] S)
    (h : f.toRingHom.AdicContinuous I J) :
    AdicCompletion I R →ₐ[T] AdicCompletion J S where
  __ := h.completionMap
  commutes' t := by
    change h.completionMap (algebraMap R (AdicCompletion I R) (algebraMap T R t)) =
      algebraMap S (AdicCompletion J S) (algebraMap T S t)
    exact (RingHom.congr_fun h.completionMap_comp (algebraMap T R t)).trans
      (congrArg (algebraMap S (AdicCompletion J S)) (f.commutes t))

/-- The algebra wrapper preserves the underlying canonical ring map. -/
@[simp]
theorem completionAlgHom_toRingHom
    {T : Type w} [CommRing T] [Algebra T R] [Algebra T S]
    (I : Ideal R) (J : Ideal S) (f : R →ₐ[T] S)
    (h : f.toRingHom.AdicContinuous I J) :
    (completionAlgHom I J f h).toRingHom = h.completionMap := rfl

/-- The completed algebra map extends the original algebra map. -/
theorem completionAlgHom_comp_algebraMap
    {T : Type w} [CommRing T] [Algebra T R] [Algebra T S]
    (I : Ideal R) (J : Ideal S) (f : R →ₐ[T] S)
    (h : f.toRingHom.AdicContinuous I J) :
    (completionAlgHom I J f h).toRingHom.comp (algebraMap R (AdicCompletion I R)) =
      (algebraMap S (AdicCompletion J S)).comp f.toRingHom := h.completionMap_comp

/-- Finite evaluation of the completed algebra map recovers the shared
finite quotient map. -/
theorem eval_completionAlgHom
    {T : Type w} [CommRing T] [Algebra T R] [Algebra T S]
    (I : Ideal R) (J : Ideal S) (f : R →ₐ[T] S)
    (h : f.toRingHom.AdicContinuous I J) (n : ℕ) :
    (evalₐ J n).toRingHom.comp (completionAlgHom I J f h).toRingHom =
      h.quotientMap n := h.eval_completionMap n

end AdicContinuous

/-- The topology-facing bridge to the completion map induced by
`RingHom.AdicContinuous`. -/
-- Local instance justification (noncanonical choice): The continuity hypothesis selects the explicitly supplied I-adic and J-adic topologies, not ambient canonical instances.
noncomputable def adicCompletionMap
    (f : R →+* S) (I : Ideal R) (J : Ideal S)
    (hcont : letI : TopologicalSpace R := I.adicTopology
             letI : TopologicalSpace S := J.adicTopology
             Continuous f) :
    AdicCompletion I R →+* AdicCompletion J S :=
  (AdicContinuous.of_continuous f I J hcont).completionMap

/-- The topology-facing completion map extends the original ring
homomorphism. -/
-- Local instance justification (noncanonical choice): The continuity hypothesis selects the explicitly supplied I-adic and J-adic topologies, not ambient canonical instances.
theorem adicCompletionMap_comp
    (f : R →+* S) (I : Ideal R) (J : Ideal S)
    (hcont : letI : TopologicalSpace R := I.adicTopology
             letI : TopologicalSpace S := J.adicTopology
             Continuous f) :
    (f.adicCompletionMap I J hcont).comp (algebraMap R (AdicCompletion I R)) =
      (algebraMap S (AdicCompletion J S)).comp f :=
  (AdicContinuous.of_continuous f I J hcont).completionMap_comp

end RingHom
