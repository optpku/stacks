/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import Mathlib.Topology.Sets.Closeds
public import stacks_project.Chap66.Lemma_66_4_6_Topology
public import stacks_project.Chap75.Definition_75_3_2_SupportedOn
public import stacks_project.Chap75.Lemma_75_13_6_PseudoCoherent
public import ReasLib.AlgebraicGeometry.AlgebraicSpace.Module.Derived.PerfectApproximation

universe u

/- Definition 75.14.1: approximation for a closed subset, a quasi-coherent derived
object, and an integer is the existence of a supported perfect approximation. -/
#check
  (AlgebraicGeometry.AlgebraicSpace.HasPerfectApproximation :
    {S : AlgebraicGeometry.Scheme.{u}} →
      {X : AlgebraicGeometry.AlgebraicSpace S} →
      (T : TopologicalSpace.Closeds (AlgebraicGeometry.AlgebraicSpace.Points X)) →
      (E : AlgebraicGeometry.AlgebraicSpace.DerivedQCoh X) →
      (m : ℤ) → Prop)

open CategoryTheory AlgebraicGeometry TopologicalSpace

#check
  (AlgebraicGeometry.AlgebraicSpace.hasPerfectApproximation_iff :
    {S : Scheme.{u}} → {X : AlgebraicSpace S} →
      (T : Closeds (AlgebraicSpace.Points X)) → (E : AlgebraicSpace.DerivedQCoh X) →
      (m : ℤ) →
      (AlgebraicSpace.HasPerfectApproximation T E m ↔
        ∃ P : AlgebraicSpace.ModuleDerived X,
          AlgebraicSpace.ModuleDerived.IsPerfect P ∧
            AlgebraicSpace.ModuleDerived.IsSupportedOn P T ∧
              ∃ α : P ⟶ E.obj,
                (∀ i : ℤ, m < i →
                  IsIso ((DerivedCategory.homologyFunctor (AlgebraicSpace.Modules X) i).map α)) ∧
                Epi ((DerivedCategory.homologyFunctor (AlgebraicSpace.Modules X) m).map α)))

#check
  (AlgebraicGeometry.AlgebraicSpace.HasPerfectApproximation.mk :
    {S : Scheme.{u}} → {X : AlgebraicSpace S} →
      {T : Closeds (AlgebraicSpace.Points X)} → {E : AlgebraicSpace.DerivedQCoh X} →
      {m : ℤ} → {P : AlgebraicSpace.ModuleDerived X} →
      (hP : AlgebraicSpace.ModuleDerived.IsPerfect P) →
      (hT : AlgebraicSpace.ModuleDerived.IsSupportedOn P T) →
      (α : P ⟶ E.obj) →
      (hiso : ∀ i : ℤ, m < i →
        IsIso ((DerivedCategory.homologyFunctor (AlgebraicSpace.Modules X) i).map α)) →
      (hepi : Epi ((DerivedCategory.homologyFunctor (AlgebraicSpace.Modules X) m).map α)) →
      AlgebraicSpace.HasPerfectApproximation T E m)

#check
  (AlgebraicGeometry.AlgebraicSpace.HasPerfectApproximation.of_iso :
    {S : Scheme.{u}} → {X : AlgebraicSpace S} →
      {T : Closeds (AlgebraicSpace.Points X)} →
      {E F : AlgebraicSpace.DerivedQCoh X} → {m : ℤ} →
      (hE : AlgebraicSpace.HasPerfectApproximation T E m) → (e : E ≅ F) →
      AlgebraicSpace.HasPerfectApproximation T F m)
