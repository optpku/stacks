/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

import StacksCheckRecall
import ReasLib.AlgebraicGeometry.Scheme.DescentData.Effectivity

open CategoryTheory

universe u v

/- Definition 35.34.11: Pulling back a scheme `U` over `S` along a family
`f i : X i ⟶ S` gives canonical descent data. A descent datum is effective
when it is isomorphic to such a canonical datum.
-/
@[stacks 02VU] #check (@AlgebraicGeometry.Scheme.DescentData.IsEffective :
  ∀ {I : Type v} {S : AlgebraicGeometry.Scheme.{u}}
    {X : I → AlgebraicGeometry.Scheme.{u}} {f : ∀ i, X i ⟶ S},
      AlgebraicGeometry.Scheme.DescentData X f → Prop)

#check (@AlgebraicGeometry.Scheme.DescentData.ofObj :
  ∀ {I : Type v} {S : AlgebraicGeometry.Scheme.{u}}
    (X : I → AlgebraicGeometry.Scheme.{u}) (f : ∀ i, X i ⟶ S),
      Over S → AlgebraicGeometry.Scheme.DescentData X f)

#check (@AlgebraicGeometry.Scheme.DescentData.ofObj_obj :
  ∀ {I : Type v} {S : AlgebraicGeometry.Scheme.{u}}
    (X : I → AlgebraicGeometry.Scheme.{u}) (f : ∀ i, X i ⟶ S)
    (U : Over S) (i : I),
      (AlgebraicGeometry.Scheme.DescentData.ofObj X f U).obj i =
        (Over.pullback (f i)).obj U)

#check (@AlgebraicGeometry.Scheme.DescentData.isEffective_iff :
  ∀ {I : Type v} {S : AlgebraicGeometry.Scheme.{u}}
    {X : I → AlgebraicGeometry.Scheme.{u}} {f : ∀ i, X i ⟶ S}
    (D : AlgebraicGeometry.Scheme.DescentData X f),
      D.IsEffective ↔
        ∃ U : Over S, Nonempty (AlgebraicGeometry.Scheme.DescentData.ofObj X f U ≅ D))

#check (@AlgebraicGeometry.Scheme.DescentData.IsEffective.ofObj :
  ∀ {I : Type v} {S : AlgebraicGeometry.Scheme.{u}}
    {X : I → AlgebraicGeometry.Scheme.{u}} {f : ∀ i, X i ⟶ S}
    (U : Over S),
      AlgebraicGeometry.Scheme.DescentData.IsEffective
        (AlgebraicGeometry.Scheme.DescentData.ofObj X f U))

#check (@AlgebraicGeometry.Scheme.DescentData.IsEffective.ofIso :
  ∀ {I : Type v} {S : AlgebraicGeometry.Scheme.{u}}
    {X : I → AlgebraicGeometry.Scheme.{u}} {f : ∀ i, X i ⟶ S}
    {D E : AlgebraicGeometry.Scheme.DescentData X f},
      (D ≅ E) → AlgebraicGeometry.Scheme.DescentData.IsEffective D →
      AlgebraicGeometry.Scheme.DescentData.IsEffective E)
