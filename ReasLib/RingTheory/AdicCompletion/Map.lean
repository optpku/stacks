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

universe u v

namespace RingHom

variable {R : Type u} {S : Type v} [CommRing R] [CommRing S]

open AdicCompletion Ideal.Quotient

namespace AdicContinuous

/-- The finite quotient map induced by an adically continuous ring
homomorphism. -/
noncomputable def quotientMap
    {I : Ideal R} {J : Ideal S} {f : R →+* S}
    (h : f.AdicContinuous I J) (n : ℕ) :
    AdicCompletion I R →+* S ⧸ J ^ n :=
  (Ideal.quotientMap (J ^ n) f
      (Ideal.map_le_iff_le_comap.mp (h.map_pow_le_pow n))).comp
    (evalₐ I (h.exponent * n))

/-- The finite quotient map extends the original ring homomorphism modulo
the prescribed target power. -/
theorem quotientMap_comp
    {I : Ideal R} {J : Ideal S} {f : R →+* S}
    (h : f.AdicContinuous I J) (n : ℕ) :
    (h.quotientMap n).comp (algebraMap R (AdicCompletion I R)) =
      (Ideal.Quotient.mk (J ^ n)).comp f := sorry

/-- The finite quotient maps induced by adic continuity commute with the
transition maps. -/
theorem quotientMap_compatible
    {I : Ideal R} {J : Ideal S} {f : R →+* S}
    (h : f.AdicContinuous I J) {m n : ℕ} (hle : m ≤ n) :
    (factorPow J hle).comp (h.quotientMap n) = h.quotientMap m := sorry

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
    (evalₐ J n).toRingHom.comp h.completionMap = h.quotientMap n := sorry

/-- The completion map induced by adic continuity extends the original ring
homomorphism. -/
theorem completionMap_comp
    {I : Ideal R} {J : Ideal S} {f : R →+* S}
    (h : f.AdicContinuous I J) :
    h.completionMap.comp (algebraMap R (AdicCompletion I R)) =
      (algebraMap S (AdicCompletion J S)).comp f := sorry

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
      (algebraMap S (AdicCompletion J S)).comp f := sorry

end RingHom
