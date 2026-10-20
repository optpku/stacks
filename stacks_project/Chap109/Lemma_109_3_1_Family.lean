/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import Mathlib.CategoryTheory.Core
public import ReasLib.AlgebraicGeometry.AlgebraicSpace.Curve.Family
public import Mathlib.CategoryTheory.ObjectProperty.FullSubcategory
public import stacks_project.Chap65.Lemma_65_7_3_Pullback
public import stacks_project.Chap99.Situation_99_15_1_Category

public import ReasLib.AlgebraicGeometry.AlgebraicSpace.Curve.FamilyOver

/-! # Families of curves over algebraic spaces -/

@[expose] public section

open CategoryTheory AlgebraicGeometry CategoryTheory.Limits
open AlgebraicGeometry.AlgebraicSpace

universe u

namespace AlgebraicGeometry.AlgebraicSpace.Spaces.Curves

/- Lemma 109.3.1: the groupoid of families over a fixed algebraic space. -/
#check (FamilyOver : {S : Scheme.{u}} → AlgebraicSpace S → Type (u + 1))

#check (familyOver_iff : ∀ {S : Scheme.{u}} {T : AlgebraicSpace S} (X : Over T),
  familyOver T X ↔ IsFamily X.hom)

#check (FamilyOver.mk : ∀ {S : Scheme.{u}} {X T : AlgebraicSpace S}
  (f : X ⟶ T) [IsFamily f], FamilyOver T)

#check (FamilyOver.space : ∀ {S : Scheme.{u}} {T : AlgebraicSpace S},
  FamilyOver T → AlgebraicSpace S)

#check (FamilyOver.hom : ∀ {S : Scheme.{u}} {T : AlgebraicSpace S}
  (P : FamilyOver T), FamilyOver.space P ⟶ T)

#check (FamilyOver.ofObj : ∀ {S : Scheme.{u}} (P : Obj S),
  FamilyOver (ofOver (base P)))

#check (instIsFamily_pullback_snd : ∀ {S : Scheme.{u}} {X Y Z : AlgebraicSpace S}
  (f : X ⟶ Y) (g : Z ⟶ Y) [IsFamily f], IsFamily (pullback.snd f g))

end AlgebraicGeometry.AlgebraicSpace.Spaces.Curves
