/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.AlgebraicGeometry.AlgebraicStack.Basic
public import ReasLib.AlgebraicGeometry.AlgebraicStack.SmoothPresentation
public import ReasLib.AlgebraicGeometry.GroupoidsOver.Algebraic
public import ReasLib.AlgebraicGeometry.GroupoidsOver.SurjectiveOnObjects

/-!
# Smooth surjective algebraic-space atlases
-/

@[expose] public section

open CategoryTheory AlgebraicGeometry
open scoped Bicategory

noncomputable section

universe u

namespace AlgebraicGeometry.AlgebraicStack

/-- A stack in groupoids over the big fppf site of a scheme is algebraic if it
admits a representable, smooth, surjective morphism from a stack representable
by an algebraic space. -/
theorem of_smooth_surjective {S : Scheme.{u}} {U X : GroupoidsOver S}
    [IsStack.InGroupoids (Scheme.fppfTopology.over S) U.p]
    [IsStack.InGroupoids (Scheme.fppfTopology.over S) X.p]
    (u : U ⟶ X) (hU : IsRepresentableByAlgebraicSpace U)
    [Groupoids.Hom.Smooth u] [Groupoids.Hom.Surjective u] :
    AlgebraicStack X :=
  sorry

/-- A stack in groupoids is algebraic if it receives an algebraic morphism from
an algebraic stack that is surjective on objects and admits a smooth
algebraic-space presentation with surjective source atlas and smooth top arrow. -/
theorem of_smooth_algebraic {S : Scheme.{u}} {X Y : GroupoidsOver S}
    [AlgebraicStack X]
    [IsStack.InGroupoids (Scheme.fppfTopology.over S) Y.p]
    (F : X ⟶ Y) [Groupoids.Hom.Algebraic F]
    [Groupoids.Hom.SurjectiveOnObjects F]
    (h_smooth : ∃ (U V : AlgebraicSpace S) (a : U.toGroupoids ⟶ X)
      (b : V.toGroupoids ⟶ Y) (h : U ⟶ V),
      IsSmoothSurjectivePresentation F a b h ∧ AlgebraicSpace.Smooth h) :
    AlgebraicStack Y := sorry

end AlgebraicGeometry.AlgebraicStack
