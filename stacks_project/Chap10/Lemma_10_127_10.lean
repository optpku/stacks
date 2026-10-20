/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import stacks_project.Chap10.Lemma_10_127_9
public import ReasLib.RingTheory.DirectLimit.Algebra.Approximation.BaseChange.Properties
public import ReasLib.RingTheory.EssentialFiniteness.Basic
public import ReasLib.RingTheory.RingHom.Local.AtPrime
import StacksCheckRecall

@[expose] public section

/-!
# Localization-of-quotient transitions in local approximations

@stack 00QU

The source-facing transition property is stated directly on the canonical
`DirectedLocalHomApproximation` data from Lemma 10.127.9.  The construction of
the directed system is deferred at the statement stage; downstream files can
use the two existence statements below without depending on proof scaffolding.
-/

universe u v w

open scoped TensorProduct

section

variable {R : Type u} {S : Type v} [CommRing R] [CommRing S]
variable [IsLocalRing R] [IsLocalRing S]
variable (f : R →+* S) [IsLocalHom f]

namespace DirectedLocalHomApproximation

/-- Source-facing spelling of the canonical ReasLib property asserting that every transition
base-change map presents its target as a localization of a quotient. -/
@[stacks 00QU "localization-of-quotient transition property"]
abbrev HasLocalizationOfQuotientTransitions {f : R →+* S}
    (A : DirectedLocalHomApproximation f) : Prop :=
  A.toApproximation.baseChange_isLocalizationOfQuotient

end DirectedLocalHomApproximation

/-- Lemma 10.127.10: a local homomorphism `R → S` that is essentially of finite type is the
pointwise colimit of a directed system of local ring maps `R_λ → S_λ` such that each `R_λ` is
essentially of finite type over `ℤ`, each `S_λ` is essentially of finite type over `R_λ`, and every
transition map `S_λ ⊗[R_λ] R_μ → S_μ` presents `S_μ` as a localization of a quotient. -/
@[stacks 00QU]
theorem exists_directed_local_essFiniteType_approximation (hf : f.EssFiniteType) :
    ∃ A : DirectedLocalHomApproximation.{u, v, u} f,
      A.HasLocalizationOfQuotientTransitions := sorry

/-- Strengthened form of Lemma 10.127.10: the directed approximation can be chosen so that all
transition maps and all stage-to-colimit comparison maps are local homomorphisms. -/
@[stacks 00QU "local-hom companion"]
theorem exists_directed_local_essFiniteType_approximation_isLocalHom (hf : f.EssFiniteType) :
    ∃ A : DirectedLocalHomApproximation.{u, v, u} f,
      A.HasLocalizationOfQuotientTransitions ∧
        (∀ i j (h : i ≤ j), IsLocalHom (A.map i j h)) ∧
          ∀ i, IsLocalHom
            (Ring.DirectLimit.toLimitHom A.RStage (fun i j h ↦ A.map i j h) A.colimitIso i) := sorry

end
