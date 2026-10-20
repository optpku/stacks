/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import Mathlib.CategoryTheory.Sites.Sheaf
public import stacks_project.Chap66.Definition_66_4_1_Points
public import stacks_project.Chap66.Definition_66_18_1_Site
public import stacks_project.Chap66.Lemma_66_16_4_Etale
public import stacks_project.Chap66.Lemma_66_18_12_Pushforward

public import ReasLib.AlgebraicGeometry.AlgebraicSpace.Sheaf.Stalk

/-!
# Pullback presentation of étale stalks at field-valued points

The stalk functor is inverse image along the point morphism followed by sections over
its source spectrum.
-/

open CategoryTheory AlgebraicGeometry
open AlgebraicGeometry.AlgebraicSpace

universe u

#check (AlgebraicGeometry.AlgebraicSpace.FieldValuedPoint.pullbackStalkFunctor :
  {S : Scheme.{u}} → {X : AlgebraicSpace S} → (p : FieldValuedPoint X) →
    [∀ F : (smallEtaleSite X)ᵒᵖ ⥤ Type (u + 1),
      (etaleBaseChange p.hom).op.HasLeftKanExtension F] →
    [HasWeakSheafify (spacesEtaleTopology (ofOver p.overObj)) (Type (u + 1))] →
    Sheaf (smallEtaleTopology X) (Type (u + 1)) ⥤ Type (u + 1))
