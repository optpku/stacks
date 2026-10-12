/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import Mathlib.Data.List.TFAE
public import Mathlib.Tactic.CrossRefAttribute
public import ReasLib.RingTheory.AdicCompletion.Map
public import ReasLib.RingTheory.Smooth.Adic.Basic

@[expose] public section

/-!
# Adic Formal Smoothness and Completion

@stack 07ED
-/

universe u v

namespace RingHom

section

variable {R : Type u} {S : Type v}
variable [CommRing R] [CommRing S]

namespace AdicContinuous

/-- Lemma 15.37.4: adic formal smoothness is invariant under finitely generated adic
completion, in the three standard source and target forms. -/
@[stacks 07ED "adic formal smoothness and completion"]
theorem formallySmooth_tfae
    {I : Ideal R} (hI : I.FG) {J : Ideal S} (hJ : J.FG)
    {f : R →+* S} (h : f.AdicContinuous I J) :
    let K := Ideal.map (algebraMap S (AdicCompletion J S)) J
    List.TFAE [
      f.formally_smooth_for_adic J,
      ((algebraMap S (AdicCompletion J S)).comp f).formally_smooth_for_adic K,
      h.completionMap.formally_smooth_for_adic K
    ] := sorry

end AdicContinuous

/-- The topology-facing form of invariance of adic formal smoothness under
finitely generated completion. -/
theorem formally_smooth_for_adic_tfae_completion_invariance
    (I : Ideal R) (hI : I.FG) (J : Ideal S) (hJ : J.FG) (f : R →+* S)
    (hcont : letI : TopologicalSpace R := I.adicTopology
             letI : TopologicalSpace S := J.adicTopology
             Continuous f) :
    let K := Ideal.map (algebraMap S (AdicCompletion J S)) J
    List.TFAE [
      f.formally_smooth_for_adic J,
      ((algebraMap S (AdicCompletion J S)).comp f).formally_smooth_for_adic K,
      (f.adicCompletionMap I J hcont).formally_smooth_for_adic K
    ] := sorry

end

end RingHom
