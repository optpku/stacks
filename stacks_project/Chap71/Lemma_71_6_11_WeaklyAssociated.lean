/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.AlgebraicGeometry.AlgebraicSpace.WeaklyAssociatedPoints
public import stacks_project.Chap66.Lemma_66_4_2_Comparison
public import stacks_project.Chap66.Lemma_66_16_4_Etale

/-!
# Weakly associated points of algebraic spaces

A point of an algebraic space is weakly associated when it is weakly associated
for the structure sheaf, witnessed on some étale scheme chart.
-/

@[expose] public section

open CategoryTheory AlgebraicGeometry

noncomputable section

universe u

namespace AlgebraicGeometry.AlgebraicSpace

#check (AlgebraicGeometry.AlgebraicSpace.weaklyAssociatedAt :
  ∀ {S : Scheme.{u}} (X : AlgebraicSpace S), Points X → Prop)

#check (AlgebraicGeometry.AlgebraicSpace.weakAss :
  ∀ {S : Scheme.{u}} (X : AlgebraicSpace S), Set (Points X))

#check (AlgebraicGeometry.AlgebraicSpace.mem_weakAss_iff :
  ∀ {S : Scheme.{u}} (X : AlgebraicSpace S) (x : Points X),
    x ∈ X.weakAss ↔ weaklyAssociatedAt X x)

end AlgebraicGeometry.AlgebraicSpace
