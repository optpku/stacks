/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import Mathlib.AlgebraicGeometry.Scheme
public import ReasLib.CategoryTheory.Bicategory.Limits.PseudoPullback.Diagonal
public import ReasLib.CategoryTheory.Bicategory.Limits.PseudoPullback.Bilimit.Lift
public import ReasLib.CategoryTheory.Fibered.BasedCategory.InGroupoids.PseudoPullback
public import ReasLib.CategoryTheory.Fibered.Groupoids.Bicategory
public import ReasLib.CategoryTheory.Fibered.TwoFibreProduct.FullSubbicategory.Bilimit

/-!
# Relative diagonals of lifted groupoid fibrations
-/

@[expose] public section

open CategoryTheory AlgebraicGeometry
open Bicategory
open scoped Bicategory
open scoped Pseudofunctor.StrongTrans

noncomputable section

universe u

namespace AlgebraicGeometry.AlgebraicSpace.CohStack

/-- The canonical relative 2-diagonal of a 1-morphism of categories fibred in
groupoids over `Over S`, in the Hom-universe of `CohStack.toGroupoids`, obtained
by universally lifting `PseudoPullbackCone.diagonal F` to the canonical self
2-fibre product. -/
noncomputable def Hom.diagonal {S : Scheme.{u}}
    {X Y : FiberedCategoryOver.Groupoids.{u + 1, u, u + 1, u + 1} (Over S)}
    (F : X ⟶ Y) :
    X ⟶ CategoryTheory.TwoFibreProduct.apex.{u + 1, u, u + 1, u + 1} F F :=
  PseudoPullbackCone.lift (PseudoPullbackCone.diagonal F)
    (CategoryTheory.TwoFibreProduct.cone.{u + 1, u, u + 1, u + 1} F F)

namespace Hom.diagonal

/-- The universal-property comparison for `Hom.diagonal F`. -/
noncomputable def comparisonIso {S : Scheme.{u}}
    {X Y : FiberedCategoryOver.Groupoids.{u + 1, u, u + 1, u + 1} (Over S)}
    (F : X ⟶ Y) :
    ((CategoryTheory.TwoFibreProduct.cone.{u + 1, u, u + 1, u + 1} F F).toPseudoCone.comparison X).obj
      (Hom.diagonal F) ≅ (PseudoPullbackCone.diagonal F).toPseudoCone.π :=
  PseudoPullbackCone.lift.comparisonIso (PseudoPullbackCone.diagonal F)
    (CategoryTheory.TwoFibreProduct.cone.{u + 1, u, u + 1, u + 1} F F)

/-- The first projection of the canonical relative 2-diagonal is isomorphic to
the identity of its source. -/
noncomputable def fstIso {S : Scheme.{u}}
    {X Y : FiberedCategoryOver.Groupoids.{u + 1, u, u + 1, u + 1} (Over S)}
    (F : X ⟶ Y) :
    Hom.diagonal F ≫
      CategoryTheory.TwoFibreProduct.fst.{u + 1, u, u + 1, u + 1} F F ≅ 𝟙 X :=
  PseudoPullbackCone.lift.fstIso (PseudoPullbackCone.diagonal F)
    (CategoryTheory.TwoFibreProduct.cone.{u + 1, u, u + 1, u + 1} F F)

/-- The second projection of the canonical relative 2-diagonal is isomorphic to
the identity of its source. -/
noncomputable def sndIso {S : Scheme.{u}}
    {X Y : FiberedCategoryOver.Groupoids.{u + 1, u, u + 1, u + 1} (Over S)}
    (F : X ⟶ Y) :
    Hom.diagonal F ≫
      CategoryTheory.TwoFibreProduct.snd.{u + 1, u, u + 1, u + 1} F F ≅ 𝟙 X :=
  PseudoPullbackCone.lift.sndIso (PseudoPullbackCone.diagonal F)
    (CategoryTheory.TwoFibreProduct.cone.{u + 1, u, u + 1, u + 1} F F)

end Hom.diagonal

end AlgebraicGeometry.AlgebraicSpace.CohStack
