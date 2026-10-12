/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import Mathlib.Tactic.CrossRefAttribute
public import stacks_project.Chap87.Lemma_87_6_4
public import stacks_project.Chap87.Lemma_87_6_5
import StacksCheckRecall

/-!
# Lemma 87.23.1

Adic and taut continuous homomorphisms of pre-adic rings, and their
equivalence on `WAdm^{adic*}`.
-/

@[expose] public section

universe u v

/- Lemma 87.23.1 (1): Let `A` and `B` be pre-adic topological rings and let
`φ : A →+* B` be a continuous ring homomorphism. If `φ` is adic, then `φ` is taut. -/
@[stacks 0GBS] #check @RingHom.IsAdicHom.isTaut

/- Lemma 87.23.1 (2): Let `A` and `B` be pre-adic topological rings and let
`φ : A →+* B` be a continuous ring homomorphism. If `B` is complete, `A` has a
finitely generated ideal of definition, and `φ` is taut, then `φ` is adic. -/
@[stacks 0GBS] #check @RingHom.IsTaut.isAdicHom

namespace RingHom

/-- Lemma 87.23.1 (3): on the category `WAdm^{adic*}` of adic rings with a
finitely generated ideal of definition, a continuous homomorphism `φ : A →+* B`
is adic if and only if it is taut. -/
@[stacks 0GBS]
theorem isAdicHom_iff_isTaut {A : Type u} {B : Type v}
    [CommRing A] [TopologicalSpace A] [TopologicalRing.IsAdicRing A]
    [CommRing B] [TopologicalSpace B] [TopologicalRing.IsAdicRing B]
    (φ : A →+* B) (hcont : Continuous φ)
    (hA : ∃ I : Ideal A, I.FG ∧ TopologicalRing.Ideal.IsIdealOfDefinition I)
    (hB : ∃ J : Ideal B, J.FG ∧ TopologicalRing.Ideal.IsIdealOfDefinition J) :
    φ.IsAdicHom ↔ φ.IsTaut :=
  sorry

end RingHom
