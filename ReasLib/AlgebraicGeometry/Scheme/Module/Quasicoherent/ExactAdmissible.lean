/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import Mathlib.CategoryTheory.Limits.ExactFunctor
public import ReasLib.AlgebraicGeometry.Scheme.Module.Quasicoherent.Admissible

@[expose] public section

open CategoryTheory
open CategoryTheory.Limits
open CategoryTheory.ObjectProperty
open AlgebraicGeometry

universe u

namespace AlgebraicGeometry.Scheme.QCoh

variable {R : Type u} [CommRing R] {X Y : Scheme.{u}}

/-- An admissible functor of quasicoherent modules is exact-admissible when it is
an exact functor `Scheme.QCoh X ⥤ Scheme.QCoh Y`. -/
class ExactAdmissible (x : X ⟶ Spec (CommRingCat.of R))
    (y : Y ⟶ Spec (CommRingCat.of R)) (F : Scheme.QCoh X ⥤ Scheme.QCoh Y) : Prop
    extends Admissible x y F where
  exact : exactFunctor (Scheme.QCoh X) (Scheme.QCoh Y) F

/-- Exact-admissibility is equivalent to admissibility together with exactness. -/
theorem exactAdmissible_iff (x : X ⟶ Spec (CommRingCat.of R))
    (y : Y ⟶ Spec (CommRingCat.of R)) (F : Scheme.QCoh X ⥤ Scheme.QCoh Y) :
    ExactAdmissible x y F ↔
      Admissible x y F ∧ exactFunctor (Scheme.QCoh X) (Scheme.QCoh Y) F := by
  constructor
  · intro h
    exact ⟨h.toAdmissible, h.exact⟩
  · rintro ⟨hA, hE⟩
    exact { toAdmissible := hA, exact := hE }

/-- The category of `R`-linear exact functors `Scheme.QCoh X ⥤ Scheme.QCoh Y`
that preserve arbitrary coproducts. -/
abbrev ExactCoproductLinearFunctor (x : X ⟶ Spec (CommRingCat.of R))
    (y : Y ⟶ Spec (CommRingCat.of R)) :=
  ObjectProperty.FullSubcategory
    fun F : Scheme.QCoh X ⥤ Scheme.QCoh Y ↦ ExactAdmissible x y F

/-- Objects of `ExactCoproductLinearFunctor` are exact-admissible functors. -/
instance exactCoproductLinearFunctor_property (x : X ⟶ Spec (CommRingCat.of R))
    (y : Y ⟶ Spec (CommRingCat.of R))
    (F : ExactCoproductLinearFunctor x y) :
    ExactAdmissible x y F.obj := F.property

end AlgebraicGeometry.Scheme.QCoh
