/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

import StacksCheckRecall
import ReasLib.AlgebraicGeometry.Scheme.DescentData.Effectivity

open CategoryTheory

universe u

variable {S X : AlgebraicGeometry.Scheme.{u}} (f : X ⟶ S)

/-
Definition 35.34.10: For a morphism `f : X ⟶ S`, specialize the family-indexed
scheme descent data to `X i = X` and `f i = f` for `i : PUnit`. The canonical datum
attached to `U : Over S` has component `Over.pullback f U`, representing `X ×_S U`,
and a datum is effective exactly when it is isomorphic to one of these canonical data.
-/
@[stacks 023Z] #check
  (AlgebraicGeometry.Scheme.DescentData.IsEffective
    (I := PUnit.{1}) (S := S) (X := fun _ ↦ X) (f := fun _ ↦ f) :
      AlgebraicGeometry.Scheme.DescentData (fun _ : PUnit.{1} ↦ X) (fun _ ↦ f) → Prop)

#check
  (AlgebraicGeometry.Scheme.DescentData.ofObj
    (I := PUnit.{1}) (S := S) (fun _ ↦ X) (fun _ ↦ f) :
      Over S →
        AlgebraicGeometry.Scheme.DescentData (fun _ : PUnit.{1} ↦ X) (fun _ ↦ f))

#check
  (AlgebraicGeometry.Scheme.DescentData.ofObj_obj
    (I := PUnit.{1}) (S := S) (fun _ ↦ X) (fun _ ↦ f) :
      ∀ (U : Over S) (i : PUnit.{1}),
        (AlgebraicGeometry.Scheme.DescentData.ofObj
          (fun _ : PUnit.{1} ↦ X) (fun _ ↦ f) U).obj i =
            (Over.pullback f).obj U)

#check
  (AlgebraicGeometry.Scheme.DescentData.isEffective_iff
    (I := PUnit.{1}) (S := S) (X := fun _ ↦ X) (f := fun _ ↦ f) :
      ∀ D : AlgebraicGeometry.Scheme.DescentData
          (fun _ : PUnit.{1} ↦ X) (fun _ ↦ f),
        D.IsEffective ↔
          ∃ U : Over S, Nonempty
            (AlgebraicGeometry.Scheme.DescentData.ofObj
              (fun _ : PUnit.{1} ↦ X) (fun _ ↦ f) U ≅ D))

#check
  (AlgebraicGeometry.Scheme.DescentData.IsEffective.ofObj
    (I := PUnit.{1}) (S := S) (X := fun _ ↦ X) (f := fun _ ↦ f) :
      ∀ U : Over S,
        AlgebraicGeometry.Scheme.DescentData.IsEffective
          (AlgebraicGeometry.Scheme.DescentData.ofObj
            (fun _ : PUnit.{1} ↦ X) (fun _ ↦ f) U))

#check
  (AlgebraicGeometry.Scheme.DescentData.IsEffective.ofIso
    (I := PUnit.{1}) (S := S) (X := fun _ ↦ X) (f := fun _ ↦ f) :
      ∀ {D E : AlgebraicGeometry.Scheme.DescentData
          (fun _ : PUnit.{1} ↦ X) (fun _ ↦ f)},
        (D ≅ E) → AlgebraicGeometry.Scheme.DescentData.IsEffective D →
          AlgebraicGeometry.Scheme.DescentData.IsEffective E)
