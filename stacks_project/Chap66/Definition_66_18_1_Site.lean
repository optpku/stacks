/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import Mathlib.AlgebraicGeometry.Sites.Etale
public import Mathlib.CategoryTheory.MorphismProperty.Comma
public import Mathlib.CategoryTheory.Sites.PrecoverageToGrothendieck
public import stacks_project.Chap07.Definition_7_6_2_Site
public import stacks_project.Chap65.Definition_65_6_3_Hom
public import stacks_project.Chap65.Lemma_65_6_2_OfOver
public import stacks_project.Chap66.Lemma_66_16_4_Etale
public import ReasLib.AlgebraicGeometry.AlgebraicSpace.EtaleSite
public import ReasLib.AlgebraicGeometry.AlgebraicSpace.EtaleSite.Presentation

/-!
# Small étale site of an algebraic space

The small étale site of an algebraic space `X` over a scheme `S` is the category of étale
morphisms from schemes over `S` into `X`, with covering families those whose underlying
families are coverings in `(Sch/S)_étale`.
-/

@[expose] public section

open CategoryTheory AlgebraicGeometry

noncomputable section

universe u

namespace AlgebraicGeometry.AlgebraicSpace

/-- The étale covering families of schemes over an algebraic space satisfy the site axioms. -/
instance smallEtalePrecoverage.instIsSite {S : Scheme.{u}} (X : AlgebraicSpace S) :
    (smallEtalePrecoverage X).IsSite where
  mem_coverings_of_isIso := Precoverage.mem_coverings_of_isIso
  hasPullbacks_of_mem := smallEtalePrecoverage.hasPullbacks_of_mem
  bind_mem := smallEtalePrecoverage.bind_mem
  pullbackArrows_mem := smallEtalePrecoverage.pullbackArrows_mem

end AlgebraicGeometry.AlgebraicSpace

#check (AlgebraicGeometry.AlgebraicSpace.smallEtaleTopology :
  ∀ {S : AlgebraicGeometry.Scheme.{u}} (X : AlgebraicGeometry.AlgebraicSpace S),
    CategoryTheory.GrothendieckTopology
      (AlgebraicGeometry.AlgebraicSpace.smallEtaleSite X))
