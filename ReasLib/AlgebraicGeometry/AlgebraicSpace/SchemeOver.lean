/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.AlgebraicGeometry.AlgebraicSpace.SchemeFunctor
public import Mathlib.CategoryTheory.Comma.StructuredArrow.Basic

/-!
# Schemes over an algebraic space

The category of schemes equipped with a morphism to an algebraic space.
-/

@[expose] public section

open CategoryTheory Opposite AlgebraicGeometry

noncomputable section

universe u

namespace AlgebraicGeometry.AlgebraicSpace

/-- The category of schemes over an algebraic space `B`, as costructured arrows for
`ofOverFunctor S`. -/
abbrev SchemeOver {S : Scheme.{u}} (B : AlgebraicSpace S) :=
  CostructuredArrow (ofOverFunctor S) B

/-- A scheme `T` over `S` equipped with a morphism `ofOver T ⟶ B`, as an object of `SchemeOver B`. -/
def SchemeOver.mk {S : Scheme.{u}} {B : AlgebraicSpace S} {T : Over S} (a : ofOver T ⟶ B) :
    SchemeOver B :=
  CostructuredArrow.mk a

/-- The underlying scheme over `S` of `SchemeOver.mk a` is the domain of `a`. -/
theorem SchemeOver.mk_left {S : Scheme.{u}} {B : AlgebraicSpace S} {T : Over S}
    (a : ofOver T ⟶ B) : (SchemeOver.mk a).left = T :=
  sorry

/-- The structural morphism of `SchemeOver.mk a` is `a`. -/
theorem SchemeOver.mk_hom {S : Scheme.{u}} {B : AlgebraicSpace S} {T : Over S}
    (a : ofOver T ⟶ B) : (SchemeOver.mk a).hom = a :=
  sorry

end AlgebraicGeometry.AlgebraicSpace

