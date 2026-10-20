/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import Mathlib.CategoryTheory.Limits.Shapes.Pullback.IsPullback.Defs
public import ReasLib.AlgebraicGeometry.AlgebraicSpace.FieldFiber
public import stacks_project.Chap65.Lemma_65_7_3_Pullback
public import stacks_project.Chap66.Definition_66_4_1_Points

/-!
# Field-valued fibres of morphisms of algebraic spaces

The fibre of a morphism `f : X ⟶ Y` of algebraic spaces over a field-valued
point `p` of `Y` is the fibre product `X ×_Y Spec(k)`, with projections to `X`
and to `Spec(k)`.
-/

@[expose] public section

open CategoryTheory AlgebraicGeometry Limits

noncomputable section

universe u

namespace AlgebraicGeometry.AlgebraicSpace

#check (AlgebraicGeometry.AlgebraicSpace.fieldFiber :
  ∀ {S : Scheme.{u}} {X Y : AlgebraicSpace S} (f : X ⟶ Y) (p : FieldValuedPoint Y),
    AlgebraicSpace S)

#check (AlgebraicGeometry.AlgebraicSpace.fieldFiber_eq :
  ∀ {S : Scheme.{u}} {X Y : AlgebraicSpace S} (f : X ⟶ Y) (p : FieldValuedPoint Y),
    fieldFiber f p = pullback f p.hom)

#check (AlgebraicGeometry.AlgebraicSpace.fieldFiberι :
  ∀ {S : Scheme.{u}} {X Y : AlgebraicSpace S} (f : X ⟶ Y) (p : FieldValuedPoint Y),
    fieldFiber f p ⟶ X)

#check (AlgebraicGeometry.AlgebraicSpace.fieldFiberι_eq :
  ∀ {S : Scheme.{u}} {X Y : AlgebraicSpace S} (f : X ⟶ Y) (p : FieldValuedPoint Y),
    fieldFiberι f p = pullback.fst f p.hom)

#check (AlgebraicGeometry.AlgebraicSpace.fieldFiberToSpec :
  ∀ {S : Scheme.{u}} {X Y : AlgebraicSpace S} (f : X ⟶ Y) (p : FieldValuedPoint Y),
    fieldFiber f p ⟶ ofOver p.overObj)

#check (AlgebraicGeometry.AlgebraicSpace.fieldFiberToSpec_eq :
  ∀ {S : Scheme.{u}} {X Y : AlgebraicSpace S} (f : X ⟶ Y) (p : FieldValuedPoint Y),
    fieldFiberToSpec f p = pullback.snd f p.hom)

#check (AlgebraicGeometry.AlgebraicSpace.fieldFiber_isPullback :
  ∀ {S : Scheme.{u}} {X Y : AlgebraicSpace S} (f : X ⟶ Y) (p : FieldValuedPoint Y),
    IsPullback (fieldFiberι f p) (fieldFiberToSpec f p) f p.hom)

#check (AlgebraicGeometry.AlgebraicSpace.fieldFiberι_comp :
  ∀ {S : Scheme.{u}} {X Y : AlgebraicSpace S} (f : X ⟶ Y) (p : FieldValuedPoint Y),
    fieldFiberι f p ≫ f = fieldFiberToSpec f p ≫ p.hom)

end AlgebraicGeometry.AlgebraicSpace
