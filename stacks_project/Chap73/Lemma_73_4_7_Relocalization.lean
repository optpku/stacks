/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

import StacksCheckRecall
public import ReasLib.AlgebraicGeometry.AlgebraicSpace.EtaleSite.Relocalization
public import stacks_project.Chap65.Lemma_65_7_3_Pullback
public import stacks_project.Chap66.Lemma_66_18_3_Site
public import stacks_project.Chap73.Definition_73_4_1_Precoverage

@[expose] public section

open CategoryTheory AlgebraicGeometry

universe u

/- Lemma 73.4.7: the canonical relocalization functor sends an étale space over
its domain to the same space over its codomain. -/
@[stacks 0DF2] #check (AlgebraicGeometry.AlgebraicSpace.Etale.SpacesToBig.relocalizationFunctor :
  ∀ {S : Scheme.{u}} {X Y : AlgebraicSpace S},
    (Y ⟶ X) → AlgebraicSpace.spacesEtaleSite Y ⥤ Over X)
