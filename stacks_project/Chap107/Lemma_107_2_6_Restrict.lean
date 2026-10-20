/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.AlgebraicGeometry.GroupoidsOver.OpenRestriction
public import ReasLib.AlgebraicGeometry.AlgebraicStack.FieldValuedPoint.Induced

/-!
# Open restriction of 2-Yoneda morphisms and induced residue-field points

Compatibility checks for open restriction and the induced residue-field point.
-/

@[expose] public section

open CategoryTheory AlgebraicGeometry
open FiberedCategoryOver.Groupoids
open GroupoidsOver
open AlgebraicGeometry.AlgebraicStack.FieldValuedPoint
open scoped Bicategory

noncomputable section

universe u

#check (AlgebraicGeometry.GroupoidsOver.restrictToOpen :
  ∀ {S : Scheme.{u}} {X : GroupoidsOver S} {U : Scheme.{u}}
    (hU : U ⟶ S) (x : X.total) (hx : X.p.obj x = Over.mk hU) (U' : U.Opens),
    GroupoidsOver.slice (Over.mk (U'.ι ≫ hU)) ⟶ X)

#check (AlgebraicGeometry.GroupoidsOver.restrictToOpen_spec :
  ∀ {S : Scheme.{u}} {X : GroupoidsOver S}
    {U : Scheme.{u}} (hU : U ⟶ S) (x : X.total)
    (hx : X.p.obj x = Over.mk hU) (U' : U.Opens),
    restrictToOpen hU x hx U' =
      overMap (Over.homMk U'.ι rfl : Over.mk (U'.ι ≫ hU) ⟶ Over.mk hU) ≫
        yonedaOfObject hU x hx)

#check (AlgebraicGeometry.AlgebraicStack.FieldValuedPoint.induced :
  ∀ {S : Scheme.{u}} {X : GroupoidsOver S} {U : Scheme.{u}} (hU : U ⟶ S) (x : X.total)
    (hx : X.p.obj x = Over.mk hU) (u0 : U),
    AlgebraicGeometry.AlgebraicStack.FieldValuedPoint X)

#check (AlgebraicGeometry.AlgebraicStack.FieldValuedPoint.induced_spec :
  ∀ {S : Scheme.{u}} {X : GroupoidsOver S} {U : Scheme.{u}} (hU : U ⟶ S) (x : X.total)
    (hx : X.p.obj x = Over.mk hU) (u0 : U),
    (induced hU x hx u0).K = residueFieldType u0 ∧
      (induced hU x hx u0).structureHom = fromResidueField u0 ≫ hU ∧
        (induced hU x hx u0).hom =
          overMap (Over.homMk (fromResidueField u0) rfl :
              Over.mk (fromResidueField u0 ≫ hU) ⟶ Over.mk hU) ≫
            yonedaOfObject hU x hx)

#check (AlgebraicGeometry.AlgebraicStack.FieldValuedPoint.instLocallyOfFiniteType_induced :
  ∀ {S : Scheme.{u}} {X : GroupoidsOver S} {U : Scheme.{u}} (hU : U ⟶ S)
    [LocallyOfFiniteType hU] (x : X.total) (hx : X.p.obj x = Over.mk hU)
    (u0 : U) [IsFiniteTypePoint u0],
    AlgebraicGeometry.LocallyOfFiniteType (induced hU x hx u0).structureHom)
