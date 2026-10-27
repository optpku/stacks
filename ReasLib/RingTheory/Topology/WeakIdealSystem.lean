/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.RingTheory.Topology.WeakIdealBasis
public import ReasLib.AlgebraicGeometry.FormalSpectrum.WeakIdeal

/-!
# Indexed fundamental systems of weak ideals

A fundamental system of weak ideals consists of weak ideals forming a neighbourhood basis of zero.
-/

@[expose] public section

universe u v

namespace TopologicalRing

/-- A family is a fundamental system of weak ideals when its members are weak ideals
of definition and form a neighbourhood basis of zero. -/
def IsFundamentalSystemOfWeakIdeals {A : Type u} [CommRing A] [TopologicalSpace A]
    {ι : Type v} (I : ι → Ideal A) : Prop :=
  (∀ i, Ideal.IsWeakIdealOfDefinition (I i)) ∧
    (nhds (0 : A)).HasBasis (fun _ : ι ↦ True) (fun i ↦ (I i : Set A))

/-- A fundamental system consists of memberwise weak ideals and a neighbourhood basis. -/
theorem isFundamentalSystemOfWeakIdeals_iff {A : Type u} [CommRing A]
    [TopologicalSpace A] {ι : Type v} (I : ι → Ideal A) :
    IsFundamentalSystemOfWeakIdeals I ↔
      (∀ i, Ideal.IsWeakIdealOfDefinition (I i)) ∧
        (nhds (0 : A)).HasBasis (fun _ : ι ↦ True) (fun i ↦ (I i : Set A)) :=
  Iff.rfl

/-- All weak ideals of definition of a weakly pre-admissible ring form a fundamental system. -/
theorem isFundamentalSystemOfWeakIdeals_all {A : Type u} [CommRing A]
    [TopologicalSpace A] [IsWeaklyPreadmissibleRing A] :
    IsFundamentalSystemOfWeakIdeals
      (fun J : AlgebraicGeometry.AffineFormalAlgebraicSpace.WeakIdealOfDefinition A ↦ J.ideal) :=
  sorry

end TopologicalRing
