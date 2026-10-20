/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import Mathlib.RingTheory.Ideal.Cotangent
public import ReasLib.RingTheory.Topology.Adic.Basic

/-!
# Cotangent modules annihilated by ideals of definition
-/

@[expose] public section

universe u

namespace TopologicalRing.Ideal

/-- An ideal `J` has cotangent annihilated by an ideal of definition if there
exists an ideal of definition `I` with `I • (⊤ : Submodule A J.Cotangent) = ⊥`.
This encodes `I (J / J ^ 2) = 0`. -/
def IsCotangentAnnihilatedByIdealOfDefinition {A : Type u} [CommRing A]
    [TopologicalSpace A] (J : Ideal A) : Prop :=
  ∃ I : Ideal A, IsIdealOfDefinition I ∧ I • (⊤ : Submodule A J.Cotangent) = ⊥

/-- An ideal has cotangent annihilated by an ideal of definition if and only if
there exists an ideal of definition `I` with
`I • (⊤ : Submodule A J.Cotangent) = ⊥`. -/
theorem isCotangentAnnihilatedByIdealOfDefinition_iff {A : Type u} [CommRing A]
    [TopologicalSpace A] (J : Ideal A) :
    IsCotangentAnnihilatedByIdealOfDefinition J ↔
      ∃ I : Ideal A, IsIdealOfDefinition I ∧
        I • (⊤ : Submodule A J.Cotangent) = ⊥ :=
  Iff.rfl

namespace IsCotangentAnnihilatedByIdealOfDefinition

/-- If `I` is an ideal of definition and `I` annihilates `J.Cotangent`, then
`J` has cotangent annihilated by an ideal of definition. -/
theorem of_smul {A : Type u} [CommRing A] [TopologicalSpace A] {J I : Ideal A}
    (hI : IsIdealOfDefinition I)
    (h : I • (⊤ : Submodule A J.Cotangent) = ⊥) :
    IsCotangentAnnihilatedByIdealOfDefinition J :=
  ⟨I, hI, h⟩

/-- If `J` has cotangent annihilated by an ideal of definition, there exists an
ideal of definition `I` with `I • (⊤ : Submodule A J.Cotangent) = ⊥`. -/
theorem spec {A : Type u} [CommRing A] [TopologicalSpace A] {J : Ideal A}
    (h : IsCotangentAnnihilatedByIdealOfDefinition J) :
    ∃ I : Ideal A, IsIdealOfDefinition I ∧
      I • (⊤ : Submodule A J.Cotangent) = ⊥ :=
  h

end IsCotangentAnnihilatedByIdealOfDefinition

end TopologicalRing.Ideal

