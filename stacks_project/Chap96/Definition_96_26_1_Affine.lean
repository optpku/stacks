/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.AlgebraicGeometry.GroupoidsOver.AffineSite

@[expose] public section

open AlgebraicGeometry CategoryTheory CategoryTheory.ObjectProperty
open AlgebraicGeometry.GroupoidsOver

universe u

/- The affine-object predicate and its membership criterion. -/
#check (AlgebraicGeometry.GroupoidsOver.affineObjects :
  ∀ {S : Scheme.{u}} (X : GroupoidsOver S), ObjectProperty X.total)
#check (AlgebraicGeometry.GroupoidsOver.affineObjects_iff :
  ∀ {S : Scheme.{u}} (X : GroupoidsOver S) (x : X.total),
    affineObjects X x ↔ IsAffine (X.p.obj x).left)

/- The affine full subcategory and its canonical inclusion. -/
#check (AlgebraicGeometry.GroupoidsOver.affineSite :
  ∀ {S : Scheme.{u}} (X : GroupoidsOver S), Type (u + 1))
#check (AlgebraicGeometry.GroupoidsOver.affineInclusion :
  ∀ {S : Scheme.{u}} (X : GroupoidsOver S), affineSite X ⥤ X.total)
#check (AlgebraicGeometry.GroupoidsOver.affineInclusion_obj :
  ∀ {S : Scheme.{u}} (X : GroupoidsOver S) (x : affineSite X),
    (affineInclusion X).obj x = x.obj)

/- The restricted projection and the affineness of its objects. -/
#check (AlgebraicGeometry.GroupoidsOver.affineToOver :
  ∀ {S : Scheme.{u}} (X : GroupoidsOver S), affineSite X ⥤ Over S)
#check (AlgebraicGeometry.GroupoidsOver.affineToOver_eq :
  ∀ {S : Scheme.{u}} (X : GroupoidsOver S),
    affineToOver X = affineInclusion X ⋙ X.p)
#check (AlgebraicGeometry.GroupoidsOver.instIsAffine :
  ∀ {S : Scheme.{u}} (X : GroupoidsOver S) (x : affineSite X),
    IsAffine (X.p.obj x.obj).left)

/- The restricted structure sheaf and its underlying presheaf. -/
#check (AlgebraicGeometry.GroupoidsOver.affineStructureSheaf :
  ∀ {S : Scheme.{u}} (X : GroupoidsOver S),
    Sheaf (⊥ : GrothendieckTopology (affineSite X)) CommRingCat.{u + 1})
#check (AlgebraicGeometry.GroupoidsOver.affineStructureSheaf_obj :
  ∀ {S : Scheme.{u}} (X : GroupoidsOver S),
    (affineStructureSheaf X).obj = Scheme.Over.commStructurePresheaf (affineToOver X))
