/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import Mathlib.CategoryTheory.Comma.Over.Basic
public import Mathlib.CategoryTheory.Whiskering
public import ReasLib.CategoryTheory.ObjectProperty.FullSubcategory.Restriction
public import stacks_project.Chap65.Lemma_65_16_1_ChangeOfBase
public import stacks_project.Chap70.Lemma_70_18_1_FinitePresentationOver
public import ReasLib.AlgebraicGeometry.AlgebraicSpace.FinitePresentation.Over.BaseChange

/-!
# Compatibility checks for finite-presentation base change

The ambient and restricted base-change APIs are supplied by shared owners.
-/

@[expose] public section

open CategoryTheory CategoryTheory.Functor CategoryTheory.ObjectProperty AlgebraicGeometry

noncomputable section

universe u

namespace AlgebraicGeometry.AlgebraicSpace

#check (AlgebraicGeometry.AlgebraicSpace.isoOfFunctorOfPoints :
  ∀ {S : Scheme.{u}} {X Y : AlgebraicSpace S},
    (X.functorOfPoints ≅ Y.functorOfPoints) → (X ≅ Y))

#check (AlgebraicGeometry.AlgebraicSpace.baseChangeMap :
  ∀ {S S' : Scheme.{u}} (g : S ⟶ S') {X Y : AlgebraicSpace S'},
    (X ⟶ Y) → (baseChange g X ⟶ baseChange g Y))

#check (AlgebraicGeometry.AlgebraicSpace.baseChangeFunctor :
  ∀ {S S' : Scheme.{u}}, (S ⟶ S') → AlgebraicSpace S' ⥤ AlgebraicSpace S)

#check (AlgebraicGeometry.AlgebraicSpace.baseChangeFunctor_obj :
  ∀ {S S' : Scheme.{u}} (g : S ⟶ S') (X : AlgebraicSpace S'),
    (baseChangeFunctor g).obj X = baseChange g X)

#check (AlgebraicGeometry.AlgebraicSpace.baseChangeFunctor_map :
  ∀ {S S' : Scheme.{u}} (g : S ⟶ S') {X Y : AlgebraicSpace S'} (α : X ⟶ Y),
    (baseChangeFunctor g).map α = baseChangeMap g α)

#check (AlgebraicGeometry.AlgebraicSpace.baseChangeFunctor_comp :
  ∀ {S S' S'' : Scheme.{u}} (f : S ⟶ S') (g : S' ⟶ S''),
    baseChangeFunctor (f ≫ g) ≅ baseChangeFunctor g ⋙ baseChangeFunctor f)

#check (AlgebraicGeometry.AlgebraicSpace.baseChange_finitePresentation :
  ∀ {S S' : Scheme.{u}} (g : S ⟶ S') (X : AlgebraicSpace S'),
    [FinitePresentation (toBase X)] → FinitePresentation (toBase (baseChange g X)))

#check (AlgebraicGeometry.AlgebraicSpace.FinitePresentationOver.mapsTo :
  ∀ {S S' : Scheme.{u}} (g : S ⟶ S'),
    finitePresentationOverProperty S' ≤
      (finitePresentationOverProperty S).inverseImage (baseChangeFunctor g))

#check (AlgebraicGeometry.AlgebraicSpace.FinitePresentationOver.baseChange :
  ∀ {S S' : Scheme.{u}}, (S ⟶ S') → FinitePresentationOver S' ⥤ FinitePresentationOver S)

#check (AlgebraicGeometry.AlgebraicSpace.FinitePresentationOver.baseChange_obj :
  ∀ {S S' : Scheme.{u}} (g : S ⟶ S') (X : FinitePresentationOver S'),
    ((FinitePresentationOver.baseChange g).obj X).obj = AlgebraicSpace.baseChange g X.obj)

#check (AlgebraicGeometry.AlgebraicSpace.FinitePresentationOver.compIso :
  ∀ {S S' S'' : Scheme.{u}} (f : S ⟶ S') (g : S' ⟶ S''),
    FinitePresentationOver.baseChange (f ≫ g) ≅
      FinitePresentationOver.baseChange g ⋙ FinitePresentationOver.baseChange f)

end AlgebraicGeometry.AlgebraicSpace
