/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import Mathlib.Algebra.Group.ULift
public import Mathlib.Algebra.GradedMonoid
public import Mathlib.Logic.Equiv.Sum
public import Mathlib.RingTheory.GradedAlgebra.Basic
public import ReasLib.Algebra.Category.ModuleCat.Sheaf.RingedSite.Graded.Quasicoherent
public import ReasLib.RingTheory.GradedAlgebra.GeneratedBy
public import stacks_project.Chap66.Definition_66_18_1_Site
public import stacks_project.Chap66.Lemma_66_18_6_Site
public import stacks_project.Chap71.Lemma_71_11_11_Triple
public import ReasLib.AlgebraicGeometry.AlgebraicSpace.RelativeProj.Functor

open CategoryTheory AlgebraicGeometry AlgebraicGeometry.AlgebraicSpace
open AlgebraicGeometry.AlgebraicSpace.RelativeProj SheafOfModules.RingedSite
universe u

/- Lemma 71.11.11: functor presentation. -/
#check (AlgebraicGeometry.AlgebraicSpace.RelativeProj.DegreeOneFunctor :
    {S : Scheme.{u}} → (X : AlgebraicSpace S) →
    GradedAlgebraSheaf.{u + 1, u} (commStructureSheafLift X) → Type (u + 1))
