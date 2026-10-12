/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import Mathlib.CategoryTheory.Functor.Basic
public import Mathlib.CategoryTheory.Opposites

/-!
# Duality base-change maps

A base-change component induces a morphism between the corresponding values of a chosen
contravariant-covariant Hom functor by functoriality in its second argument.
-/

@[expose] public section

open CategoryTheory

universe u v

namespace CategoryTheory.Functor.DualityBaseChange

variable {D_Y D_X D_Y' D_X' D_R : Type u}
variable [Category.{v} D_Y] [Category.{v} D_X] [Category.{v} D_Y']
variable [Category.{v} D_X'] [Category.{v} D_R]

/-- Applying a chosen contravariant-covariant Hom functor, with its first argument fixed,
to a base-change component in the second argument. -/
def rHomMap
    (gPull : D_Y ⥤ D_Y') (gPrimePull : D_X ⥤ D_X')
    (a : D_Y ⥤ D_X) (aPrime : D_Y' ⥤ D_X')
    (rHom : D_X'ᵒᵖ ⥤ D_X' ⥤ D_R) (M : D_X) (K : D_Y)
    (baseChange : gPrimePull.obj (a.obj K) ⟶ aPrime.obj (gPull.obj K)) :
    (rHom.obj (Opposite.op (gPrimePull.obj M))).obj (gPrimePull.obj (a.obj K)) ⟶
      (rHom.obj (Opposite.op (gPrimePull.obj M))).obj (aPrime.obj (gPull.obj K)) :=
  (rHom.obj (Opposite.op (gPrimePull.obj M))).map baseChange

end CategoryTheory.Functor.DualityBaseChange
