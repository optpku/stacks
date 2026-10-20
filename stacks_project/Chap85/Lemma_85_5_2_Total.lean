/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import Mathlib.CategoryTheory.Adjunction.Mates
public import ReasLib.CategoryTheory.Sites.Topos.Composition
public import stacks_project.Chap85.Lemma_85_3_5
public import stacks_project.Chap85.Remark_85_5_1_Morphism

public import ReasLib.CategoryTheory.Sites.Simplicial.TotalMorphism

/-!
# Total morphisms of covariant simplicial sites

The total morphism and its degree comparisons are provided by the shared site API.
-/

@[expose] public section

universe u v

open CategoryTheory

/- Lemma 85.5.2 -/
#check (CategoryTheory.SimplicialSites.IsMorphism.totalFunctor :
  ∀ {C C' : SimplexCategory ⥤ Cat.{v, u}}, (C' ⟶ C) →
    SimplicialSites.totalSite C' ⥤ SimplicialSites.totalSite C)
