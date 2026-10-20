/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import Mathlib.CategoryTheory.Limits.ExactFunctor
public import Mathlib.CategoryTheory.Limits.Shapes.Products
public import Mathlib.CategoryTheory.ObjectProperty.FullSubcategory
public import ReasLib.AlgebraicGeometry.Scheme.Module.Quasicoherent.Linearity

@[expose] public section

open CategoryTheory
open CategoryTheory.Limits
open CategoryTheory.ObjectProperty
open AlgebraicGeometry

universe u

namespace AlgebraicGeometry.Scheme.QCoh

variable {R : Type u} [CommRing R] {X Y : Scheme.{u}}

/-- An `R`-linear functor of quasicoherent modules is admissible when it is
right exact and preserves arbitrary coproducts indexed by `Type u`. -/
class Admissible (x : X ⟶ Spec (CommRingCat.of R))
    (y : Y ⟶ Spec (CommRingCat.of R)) (F : Scheme.QCoh X ⥤ Scheme.QCoh Y) : Prop
    extends LinearOver x y F where
  rightExact : rightExactFunctor (Scheme.QCoh X) (Scheme.QCoh Y) F
  preservesCoproducts : ∀ J : Type u, PreservesColimitsOfShape (Discrete J) F

/-- Admissibility is equivalent to relative `R`-linearity, right exactness, and
preservation of `Type u`-indexed coproducts. -/
theorem admissible_iff (x : X ⟶ Spec (CommRingCat.of R))
    (y : Y ⟶ Spec (CommRingCat.of R)) (F : Scheme.QCoh X ⥤ Scheme.QCoh Y) :
    Admissible x y F ↔
      LinearOver x y F ∧
        rightExactFunctor (Scheme.QCoh X) (Scheme.QCoh Y) F ∧
          ∀ J : Type u, PreservesColimitsOfShape (Discrete J) F := sorry

/-- The category of admissible `R`-linear, right-exact, coproduct-preserving
functors `Scheme.QCoh X ⥤ Scheme.QCoh Y`. -/
abbrev RightExactCoproductLinearFunctor (x : X ⟶ Spec (CommRingCat.of R))
    (y : Y ⟶ Spec (CommRingCat.of R)) :=
  ObjectProperty.FullSubcategory
    fun F : Scheme.QCoh X ⥤ Scheme.QCoh Y ↦ Admissible x y F

/-- Objects of `RightExactCoproductLinearFunctor` are admissible functors. -/
instance functorCategory_property (x : X ⟶ Spec (CommRingCat.of R))
    (y : Y ⟶ Spec (CommRingCat.of R))
    (F : RightExactCoproductLinearFunctor x y) :
    Admissible x y F.obj := F.property

end AlgebraicGeometry.Scheme.QCoh
