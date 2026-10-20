/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.AlgebraicGeometry.Scheme.SmallBoundClosed
public import stacks_project.Chap03.«3_9_1_1_Bound»

@[expose] public section

universe u

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits
open AlgebraicGeometry.Scheme
open scoped Cardinal AlgebraicGeometry

#check (AlgebraicGeometry.Scheme.IsSmallBoundClosed.isoClosure_of_size_le_bound :
  ∀ {P : ObjectProperty Scheme.{u}}, IsSmallBoundClosed P →
    ∀ {S T : Scheme.{u}}, P S → T.size ≤ bound S.size → P.isoClosure T)

#check (AlgebraicGeometry.Scheme.IsSmallBoundClosed.hasLimit_iff :
  ∀ {P : ObjectProperty Scheme.{u}}, IsSmallBoundClosed P →
    ∀ {J : Type} [SmallCategory J] [CountableCategory J]
      (F : J ⥤ P.FullSubcategory), HasLimit F ↔ HasLimit (F ⋙ P.ι))

#check (AlgebraicGeometry.Scheme.IsSmallBoundClosed.isIso_limit_post :
  ∀ {P : ObjectProperty Scheme.{u}}, IsSmallBoundClosed P →
    ∀ {J : Type} [SmallCategory J] [CountableCategory J]
      (F : J ⥤ P.FullSubcategory) [HasLimit F] [HasLimit (F ⋙ P.ι)],
      IsIso (limit.post F P.ι))

#check (AlgebraicGeometry.Scheme.IsSmallBoundClosed.hasColimit_iff :
  ∀ {P : ObjectProperty Scheme.{u}}, IsSmallBoundClosed P →
    ∀ {J : Type} [SmallCategory J] [CountableCategory J]
      (F : J ⥤ P.FullSubcategory), HasColimit F ↔ HasColimit (F ⋙ P.ι))

#check (AlgebraicGeometry.Scheme.IsSmallBoundClosed.isIso_colimit_post :
  ∀ {P : ObjectProperty Scheme.{u}}, IsSmallBoundClosed P →
    ∀ {J : Type} [SmallCategory J] [CountableCategory J]
      (F : J ⥤ P.FullSubcategory) [HasColimit F] [HasColimit (F ⋙ P.ι)],
      IsIso (colimit.post F P.ι))
