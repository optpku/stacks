/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.AlgebraicGeometry.AlgebraicStack.Gerbe.Fppf
import StacksCheckRecall

/-!
# Gerbes have fppf inertia, diagonal, and Isom comparisons

If `f : X ⟶ Y` makes `X` a gerbe over `Y`, then the relative inertia morphism
is flat and locally of finite presentation, and the relative 2-diagonal,
fibre-product comparisons, and Isom comparisons are surjective, flat, and
locally of finite presentation.
-/

@[expose] public section

open CategoryTheory AlgebraicGeometry
open FiberedCategoryOver.Groupoids
open scoped Bicategory

noncomputable section

universe u

namespace AlgebraicGeometry.AlgebraicStack

/- Lemma 101.28.10 (1): the relative inertia projection is flat and locally of finite presentation.
-/
@[stacks 0CPR] #check (AlgebraicGeometry.AlgebraicStack.RelativeInertia.forget_flat_locallyOfFinitePresentation
    : ∀ {S : Scheme.{u}}
    {X Y : GroupoidsOver S} [AlgebraicStack X] [AlgebraicStack Y]
    (f : X ⟶ Y) [Gerbe f],
    Flat (FiberedCategoryOver.Groupoids.RelativeInertia.forget.{u + 1, u, u, u + 1} f) ∧
      LocallyOfFinitePresentation (FiberedCategoryOver.Groupoids.RelativeInertia.forget.{u + 1, u, u, u + 1} f))

/- Lemma 101.28.10 (2): the relative 2-diagonal is surjective, flat, and locally of finite presentation.
-/
@[stacks 0CPR] #check (AlgebraicGeometry.AlgebraicStack.diagonal_surjective_flat_locallyOfFinitePresentation
    : ∀ {S : Scheme.{u}} {X Y : GroupoidsOver S}
    [AlgebraicStack X] [AlgebraicStack Y] (f : X ⟶ Y) [Gerbe f],
    Surjective (Hom.diagonal.{u + 1, u, u + 1} f) ∧
      Flat (Hom.diagonal.{u + 1, u, u + 1} f) ∧
        LocallyOfFinitePresentation (Hom.diagonal.{u + 1, u, u + 1} f))

/- Lemma 101.28.10 (3): the two-fibre-product comparison is surjective, flat, and locally of finite presentation.
-/
@[stacks 0CPR] #check (AlgebraicGeometry.AlgebraicStack.fibreProductComparison_of_gerbe
    : ∀ {S : Scheme.{u}}
    {X Y : GroupoidsOver S} [AlgebraicStack X] [AlgebraicStack Y]
    (f : X ⟶ Y) [Gerbe f] {T1 T2 : AlgebraicSpace S}
    (x1 : T1.toGroupoids ⟶ X) (x2 : T2.toGroupoids ⟶ X),
    Surjective (TwoFibreProduct.mapPostcompose.{u + 1, u, u + 1, u} x1 x2 f) ∧
      Flat (TwoFibreProduct.mapPostcompose.{u + 1, u, u + 1, u} x1 x2 f) ∧
        LocallyOfFinitePresentation (TwoFibreProduct.mapPostcompose.{u + 1, u, u + 1, u} x1 x2 f))

/- Lemma 101.28.10 (4): the Isom comparison is surjective, flat, and locally of finite presentation.
-/
@[stacks 0CPR] #check (AlgebraicGeometry.AlgebraicStack.isomComparison_of_gerbe
    : ∀ {S : Scheme.{u}} {X Y : GroupoidsOver S}
    [AlgebraicStack X] [AlgebraicStack Y] (f : X ⟶ Y) [Gerbe f]
    {T : AlgebraicSpace S} (x1 x2 : T.toGroupoids ⟶ X),
    Groupoids.Hom.has (@AlgebraicSpace.Surjective S) (isomComparison f x1 x2) ∧
      Groupoids.Hom.has (@AlgebraicSpace.Flat S) (isomComparison f x1 x2) ∧
        Groupoids.Hom.has (@AlgebraicSpace.LocallyOfFinitePresentation S)
          (isomComparison f x1 x2))

end AlgebraicGeometry.AlgebraicStack
