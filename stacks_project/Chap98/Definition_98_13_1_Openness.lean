/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.AlgebraicGeometry.GroupoidsOver.OpennessOfVersality
public import Mathlib.CategoryTheory.Comma.Over.Basic
public import ReasLib.CategoryTheory.Fibered.Groupoids.SliceBaseChange
public import ReasLib.CategoryTheory.Fibered.InGroupoids.Composition
public import stacks_project.Chap98.Definition_98_13_1_Versal

/-!
# Openness of versality

Compatibility checks for the canonical openness of versality API.
-/

@[expose] public section

open CategoryTheory AlgebraicGeometry TopologicalSpace
open AlgebraicGeometry.GroupoidsOver
open FiberedCategoryOver.Groupoids
open scoped Bicategory

noncomputable section

universe u

#check (AlgebraicGeometry.GroupoidsOver.OpennessOfVersality :
  ∀ {S : Scheme.{u}} [IsLocallyNoetherian S]
    (X : GroupoidsOver S),
    Prop)

#check (AlgebraicGeometry.GroupoidsOver.fiberProductSlice :
  ∀ {S : Scheme.{u}} {X Y : GroupoidsOver S} (f : X ⟶ Y)
    {U : Scheme.{u}} (hU : U ⟶ S) (y : Y.total)
    (hy : Y.p.obj y = Over.mk hU),
    GroupoidsOver U)

#check (AlgebraicGeometry.GroupoidsOver.fiberProductSlice_total :
  ∀ {S : Scheme.{u}} {X Y : GroupoidsOver S}
    (f : X ⟶ Y) {U : Scheme.{u}} (hU : U ⟶ S) (y : Y.total)
    (hy : Y.p.obj y = Over.mk hU),
    (fiberProductSlice f hU y hy).total =
      (FiberedCategoryOver.Groupoids.baseChange f (yonedaOfObject hU y hy)).total)

#check (AlgebraicGeometry.GroupoidsOver.fiberProductSlice_spec :
  ∀ {S : Scheme.{u}} {X Y : GroupoidsOver S}
    (f : X ⟶ Y) {U : Scheme.{u}} (hU : U ⟶ S) (y : Y.total)
    (hy : Y.p.obj y = Over.mk hU),
    (fiberProductSlice f hU y hy).toBasedCategory =
      BasedCategory.ofFunctor
        ((FiberedCategoryOver.Groupoids.baseChange f (yonedaOfObject hU y hy)).p ⋙
          Over.iteratedSliceForward (Over.mk hU)))

#check (AlgebraicGeometry.GroupoidsOver.OpennessOfVersality.slice :
  ∀ {S : Scheme.{u}} [IsLocallyNoetherian S] (V : Over S)
    [LocallyOfFiniteType V.hom],
    OpennessOfVersality (GroupoidsOver.slice V))

#check (AlgebraicGeometry.GroupoidsOver.OpennessOfVersality.spec :
  ∀ {S : Scheme.{u}} [IsLocallyNoetherian S] (X : GroupoidsOver S)
    [OpennessOfVersality X] {U : Scheme.{u}} (hU : U ⟶ S)
    [LocallyOfFiniteType hU] (x : X.total) (hx : X.p.obj x = Over.mk hU)
    (u0 : U) (hu0 : IsFiniteTypePoint u0) (hvers : IsVersalAt hU x hx u0),
    ∃ U' : Opens U, u0 ∈ U' ∧
      ∀ u : U, u ∈ U' → IsFiniteTypePoint u → IsVersalAt hU x hx u)

#check (AlgebraicGeometry.GroupoidsOver.OpennessOfVersality.iff :
  ∀ {S : Scheme.{u}} [IsLocallyNoetherian S] (X : GroupoidsOver S),
    OpennessOfVersality X ↔
      ∀ {U : Scheme.{u}} (hU : U ⟶ S) [LocallyOfFiniteType hU] (x : X.total)
        (hx : X.p.obj x = Over.mk hU) (u0 : U), IsFiniteTypePoint u0 →
        IsVersalAt hU x hx u0 →
          ∃ U' : Opens U, u0 ∈ U' ∧
            ∀ u : U, u ∈ U' → IsFiniteTypePoint u → IsVersalAt hU x hx u)

namespace AlgebraicGeometry.Groupoids.Hom

#check (AlgebraicGeometry.Groupoids.Hom.OpennessOfVersality :
  ∀ {S : Scheme.{u}} [IsLocallyNoetherian S]
    {X Y : GroupoidsOver S} (f : X ⟶ Y),
    Prop)

#check (AlgebraicGeometry.Groupoids.Hom.OpennessOfVersality.id :
  ∀ {S : Scheme.{u}} [IsLocallyNoetherian S] {X : GroupoidsOver S},
    OpennessOfVersality (𝟙 X))

#check (AlgebraicGeometry.Groupoids.Hom.OpennessOfVersality.spec :
  ∀ {S : Scheme.{u}} [IsLocallyNoetherian S] {X Y : GroupoidsOver S}
    (f : X ⟶ Y) [OpennessOfVersality f] {U : Scheme.{u}} (hU : U ⟶ S)
    [LocallyOfFiniteType hU] [IsLocallyNoetherian U] (y : Y.total)
    (hy : Y.p.obj y = Over.mk hU),
    GroupoidsOver.OpennessOfVersality (fiberProductSlice f hU y hy))

#check (AlgebraicGeometry.Groupoids.Hom.OpennessOfVersality.iff :
  ∀ {S : Scheme.{u}} [IsLocallyNoetherian S] {X Y : GroupoidsOver S}
    (f : X ⟶ Y),
    OpennessOfVersality f ↔
      ∀ {U : Scheme.{u}} (hU : U ⟶ S) [LocallyOfFiniteType hU]
        [IsLocallyNoetherian U] (y : Y.total) (hy : Y.p.obj y = Over.mk hU),
        GroupoidsOver.OpennessOfVersality (fiberProductSlice f hU y hy))

end AlgebraicGeometry.Groupoids.Hom
