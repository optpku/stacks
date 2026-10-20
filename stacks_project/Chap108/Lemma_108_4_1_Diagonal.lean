/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.CategoryTheory.Fibered.Groupoids.Diagonal.Construction
public import stacks_project.Chap110.Lemma_110_53_1

/-!
# Relative 2-diagonals of CohStack-sized groupoid fibrations

The canonical relative 2-diagonal of a 1-morphism in
`FiberedCategoryOver.Groupoids.{u + 1, u, u + 1, u + 1} (Over S)`, obtained by
universally lifting the diagonal pseudo-pullback cone to the canonical self
2-fibre product. This is the Hom-universe of `CohStack.toGroupoids`, which does
not land in `GroupoidsOver S`.
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
  PseudoPullbackCone.lift
    (PseudoPullbackCone.diagonal F)
    (CategoryTheory.TwoFibreProduct.cone.{u + 1, u, u + 1, u + 1} F F)

namespace Hom.diagonal

/-- The universal-property comparison for `Hom.diagonal F`. -/
noncomputable def comparisonIso {S : Scheme.{u}}
    {X Y : FiberedCategoryOver.Groupoids.{u + 1, u, u + 1, u + 1} (Over S)}
    (F : X ⟶ Y) :
    ((CategoryTheory.TwoFibreProduct.cone.{u + 1, u, u + 1, u + 1} F F).toPseudoCone.comparison
        X).obj
      (Hom.diagonal F) ≅
      (PseudoPullbackCone.diagonal F).toPseudoCone.π :=
  PseudoPullbackCone.lift.comparisonIso
    (PseudoPullbackCone.diagonal F)
    (CategoryTheory.TwoFibreProduct.cone.{u + 1, u, u + 1, u + 1} F F)

/-- The first projection of the canonical relative 2-diagonal is isomorphic to
the identity of its source. -/
noncomputable def fstIso {S : Scheme.{u}}
    {X Y : FiberedCategoryOver.Groupoids.{u + 1, u, u + 1, u + 1} (Over S)}
    (F : X ⟶ Y) :
    Hom.diagonal F ≫
      CategoryTheory.TwoFibreProduct.fst.{u + 1, u, u + 1, u + 1} F F ≅ 𝟙 X :=
  PseudoPullbackCone.lift.fstIso
    (PseudoPullbackCone.diagonal F)
    (CategoryTheory.TwoFibreProduct.cone.{u + 1, u, u + 1, u + 1} F F)

/-- The second projection of the canonical relative 2-diagonal is isomorphic to
the identity of its source. -/
noncomputable def sndIso {S : Scheme.{u}}
    {X Y : FiberedCategoryOver.Groupoids.{u + 1, u, u + 1, u + 1} (Over S)}
    (F : X ⟶ Y) :
    Hom.diagonal F ≫
      CategoryTheory.TwoFibreProduct.snd.{u + 1, u, u + 1, u + 1} F F ≅ 𝟙 X :=
  PseudoPullbackCone.lift.sndIso
    (PseudoPullbackCone.diagonal F)
    (CategoryTheory.TwoFibreProduct.cone.{u + 1, u, u + 1, u + 1} F F)

end Hom.diagonal

end AlgebraicGeometry.AlgebraicSpace.CohStack
