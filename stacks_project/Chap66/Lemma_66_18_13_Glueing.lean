module

public import ReasLib.AlgebraicGeometry.AlgebraicSpace.EtaleSite.Glueing
public import ReasLib.AlgebraicGeometry.AlgebraicSpace.EtaleSite.IdentityChart
public import Mathlib.CategoryTheory.Category.Cat
public import Mathlib.CategoryTheory.Sites.Continuous
public import stacks_project.Chap66.Definition_66_4_1_Points
public import stacks_project.Chap66.Definition_66_18_1_Site
public import stacks_project.Chap66.Lemma_66_16_4_Etale
public import stacks_project.Chap66.Lemma_66_18_8_Topos
public import stacks_project.Chap66.Lemma_66_18_11

/-! Compatibility imports for the source-facing small étale glueing API. -/

@[expose] public section

open CategoryTheory AlgebraicGeometry Opposite

universe u

/- The chart identity API remains available through this source-facing module. -/
#check (AlgebraicGeometry.AlgebraicSpace.SmallEtaleGlueing.ofOverMap_id :
  ∀ {S : Scheme.{u}} (U : Over S),
    AlgebraicGeometry.AlgebraicSpace.ofOverMap (𝟙 U) =
      𝟙 (AlgebraicGeometry.AlgebraicSpace.ofOver U))
