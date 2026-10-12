/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import Mathlib.Data.List.TFAE
public import stacks_project.Chap88.Lemma_88_15_1_FlatAway
import Mathlib.Tactic.CrossRefAttribute

/-!
# Equivalence of away and prime tests for adic flatness

An adic morphism of objects of `WAdm^{adic*}` is flat after inverting
topologically nilpotent elements of the source if and only if the same holds
after inverting topologically nilpotent elements of the target, and if and only
if the target is flat over the source at primes containing no ideal of
definition, equivalently at every rig-closed prime.
-/

@[expose] public section

universe u

namespace RingHom

variable {A B : Type u} [CommRing A] [CommRing B]
variable [TopologicalSpace A] [TopologicalSpace B]
variable [TopologicalRing.IsAdicRing A] [TopologicalRing.IsAdicRing B]

/-- Lemma 88.15.1: for an adic morphism `φ : A →+* B` in `WAdm^{adic*}`
(adic topological rings with a finitely generated ideal of definition), the
following are equivalent: `B_f` is flat over `A` for every topologically
nilpotent `f` in `A`; `B_g` is flat over `A` for every topologically nilpotent
`g` in `B`; `B_q` is flat over `A` for every prime `q` of `B` containing no
ideal of definition; and `B_q` is flat over `A` for every rig-closed prime `q`
of `B`. The Stacks placeholder clause (5) is omitted. -/
@[stacks 0GGL]
theorem isFlatAwayTopologicallyNilpotent_tfae (φ : A →+* B) (hφ : φ.IsAdicHom)
    (hA : ∃ I : Ideal A, I.FG ∧ TopologicalRing.Ideal.IsIdealOfDefinition I)
    (hB : ∃ J : Ideal B, J.FG ∧ TopologicalRing.Ideal.IsIdealOfDefinition J) :
    List.TFAE [φ.IsFlatAwayTopologicallyNilpotent, φ.IsFlatAwayTargetTopologicallyNilpotent,
      φ.IsFlatAtPrimesAvoidingIdealOfDefinition, φ.IsFlatAtRigClosed] :=
  sorry

end RingHom
