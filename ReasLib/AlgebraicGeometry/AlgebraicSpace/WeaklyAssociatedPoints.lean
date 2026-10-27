/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.AlgebraicGeometry.Scheme.WeaklyAssociatedPoints
public import ReasLib.AlgebraicGeometry.AlgebraicSpace.Points.Comparison
public import ReasLib.AlgebraicGeometry.AlgebraicSpace.Etale
public import ReasLib.AlgebraicGeometry.AlgebraicSpace.Module.WeaklyAssociatedPoints

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

/-- A point of an algebraic space is weakly associated when some étale morphism
from a scheme has a weakly associated point mapping to it. -/
def weaklyAssociatedAt {S : Scheme.{u}} (X : AlgebraicSpace S) (x : Points X) :
    Prop :=
  ∃ (U : Over S) (a : ofOver U ⟶ X) (u : U.left),
    Etale a ∧ Points.map a (ofOver.pointsEquiv U u) = x ∧ u ∈ U.left.weakAss

/-- The set of weakly associated points of an algebraic space. -/
def weakAss {S : Scheme.{u}} (X : AlgebraicSpace S) : Set (Points X) :=
  {x | weaklyAssociatedAt X x}

/-- Membership in `X.weakAss` is the étale-chart weakly-associated-point
predicate. -/
theorem mem_weakAss_iff {S : Scheme.{u}} (X : AlgebraicSpace S) (x : Points X) :
    x ∈ X.weakAss ↔ weaklyAssociatedAt X x :=
  Iff.rfl

/-- The weakly associated locus of an algebraic space equals the weakly associated locus of
its structure sheaf. -/
theorem weakAss_eq_weakAss_unit {S : Scheme.{u}} (X : AlgebraicSpace S) :
    X.weakAss = Modules.weakAss (SheafOfModules.unit (structureSheaf X) : X.Modules) :=
  sorry

/-- A point is weakly associated to an algebraic space exactly when its structure sheaf
satisfies the étale-stalk weak-association condition there. -/
theorem mem_weakAss_iff_etaleStalkWeakAss {S : Scheme.{u}} (X : AlgebraicSpace S)
    (x : Points X) :
    x ∈ X.weakAss ↔
      Modules.etaleStalkWeakAss (SheafOfModules.unit (structureSheaf X) : X.Modules) x := by
  rw [weakAss_eq_weakAss_unit X]
  exact Modules.mem_weakAss_iff _ x

end AlgebraicGeometry.AlgebraicSpace
