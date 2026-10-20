/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.AlgebraicGeometry.AlgebraicStack.CoveringFamilyLift
import StacksCheckRecall

open CategoryTheory AlgebraicGeometry
open scoped Bicategory

universe u v

/- Lemma 101.27.14: A jointly surjective family of flat, locally finitely
presented morphisms of algebraic stacks admits fppf-local lifts of every
target object, with each covering member assigned to a source in the family
and its lifted image isomorphic to the canonical restriction. -/
@[stacks 07AN] #check
  (AlgebraicGeometry.AlgebraicStack.exists_fppfCoveringFamily_iso :
    ∀ {S : Scheme.{u}} {X : GroupoidsOver S} [AlgebraicStack X]
      {J : Type v} {Xj : J → GroupoidsOver S} [∀ j, AlgebraicStack (Xj j)]
      (f : ∀ j, Xj j ⟶ X) [∀ j, AlgebraicStack.Flat (f j)]
      [∀ j, AlgebraicStack.LocallyOfFinitePresentation (f j)],
      (∀ y : AlgebraicStack.Points X,
        ∃ j, y ∈ Set.range (AlgebraicStack.Points.map (f j))) →
      ∀ {U : Over S} (x : GroupoidsOver.slice U ⟶ X),
        Groupoids.Hom.existsCoveringFamilyLift StandardTopology.fppf f x)
