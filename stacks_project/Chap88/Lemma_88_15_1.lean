/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.RingTheory.Flat.Adic
import StacksCheckRecall

/-!
# Equivalence of away and prime tests for adic flatness
-/

universe u

/- Lemma 88.15.1: the four flatness tests for an adic morphism of complete
separated adic rings with finitely generated ideals of definition are equivalent.
The editorial placeholder for a fifth condition is omitted. -/
@[stacks 0GGL] #check (RingHom.isFlatAwayTopologicallyNilpotent_tfae :
  ∀ {A B : Type u} [CommRing A] [CommRing B]
    [TopologicalSpace A] [TopologicalSpace B]
    [TopologicalRing.IsAdicRing A] [TopologicalRing.IsAdicRing B]
    (φ : A →+* B) (hφ : φ.IsAdicHom)
    (hA : ∃ I : Ideal A, I.FG ∧ TopologicalRing.Ideal.IsIdealOfDefinition I)
    (hB : ∃ J : Ideal B, J.FG ∧ TopologicalRing.Ideal.IsIdealOfDefinition J),
    List.TFAE [φ.IsFlatAwayTopologicallyNilpotent, φ.IsFlatAwayTargetTopologicallyNilpotent,
      φ.IsFlatAtPrimesAvoidingIdealOfDefinition, φ.IsFlatAtRigClosed])
