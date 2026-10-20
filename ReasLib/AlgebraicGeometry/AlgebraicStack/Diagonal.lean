/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.AlgebraicGeometry.GroupoidsOver.Diagonal.Pullback
public import ReasLib.AlgebraicGeometry.AlgebraicStack.Basic

/-!
# Fibre squares of Isom sheaves along diagonals

For a morphism of algebraic stacks, the 2-fibre product of the diagonal
against a 2-Yoneda triple `(x, x', α)` is cartesian as a square of sheaves
over `T`.
-/

@[expose] public section

open CategoryTheory AlgebraicGeometry Opposite
open FiberedCategoryOver.Groupoids
open CategoryTheory.FiberedCategoryOver.Groupoids.Hom.diagonal
open CategoryTheory.Limits
open scoped Bicategory

noncomputable section

universe u

namespace AlgebraicGeometry.AlgebraicStack

/-- For a morphism of algebraic stacks, the canonical Isom comparison square of the
diagonal base change along a Yoneda triple is cartesian. -/
theorem isomSquare_isPullback {S : Scheme.{u}} {X Y : GroupoidsOver S}
    [AlgebraicStack X] [AlgebraicStack Y] (f : X ⟶ Y) {T : Over S}
    (x x' : X.p.Fiber T)
    (α : (fiberFunctor f T).obj x ≅ (fiberFunctor f T).obj x') :
    IsPullback (toIsom f x x' α) (toBase f x x' α)
      (isomMap f x x') (alphaSection f x x' α) :=
  sorry

/-- The Isom presheaf of two fibre objects of an algebraic stack is a sheaf on the
slice fppf topology. -/
theorem diagonal_isom_isSheaf {S : Scheme.{u}} {X : GroupoidsOver S}
    [AlgebraicStack X] {T : Over S} (x x' : X.p.Fiber T) :
    Presheaf.IsSheaf ((Scheme.fppfTopology.over S).over T) (isom x x') :=
  sorry

/-- The lifted presheaf represented by the identity slice is a sheaf on the
slice fppf topology. -/
theorem diagonal_base_isSheaf {S : Scheme.{u}} (T : Over S) :
    Presheaf.IsSheaf ((Scheme.fppfTopology.over S).over T)
      (yoneda.obj (Over.mk (𝟙 T)) ⋙ uliftFunctor.{u + 1, u}) :=
  sorry

/-- The fibre-isomorphism-class presheaf of the diagonal base change of a morphism
of algebraic stacks is a sheaf on the slice fppf topology. -/
theorem diagonal_apexSheaf_isSheaf {S : Scheme.{u}} {X Y : GroupoidsOver S}
    [AlgebraicStack X] [AlgebraicStack Y] (f : X ⟶ Y) {T : Over S}
    (x x' : X.p.Fiber T)
    (α : (fiberFunctor f T).obj x ≅ (fiberFunctor f T).obj x') :
    Presheaf.IsSheaf ((Scheme.fppfTopology.over S).over T) (apexSheaf f x x' α) :=
  sorry

end AlgebraicGeometry.AlgebraicStack
