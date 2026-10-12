/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import stacks_project.Chap101.Definition_101_28_1_Gerbe
public import stacks_project.Chap67.Definition_67_5_2_Surjective
public import stacks_project.Chap101.Lemma_101_25_5_Surjective
public import stacks_project.Chap101.Lemma_101_25_5_Flat
public import stacks_project.Chap106.Lemma_106_10_1_LocallyOfFinitePresentation
public import stacks_project.Chap101.Lemma_101_5_1
public import stacks_project.Chap101.Lemma_101_6_6_Comparison
public import stacks_project.Chap101.Lemma_101_6_6_Isom
public import stacks_project.Chap94.Lemma_94_14_3_Pullback

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

namespace RelativeInertia

open FiberedCategoryOver.Groupoids.RelativeInertia (forget)

/-- Lemma 101.28.10 (1): if `f : X ⟶ Y` is a gerbe of algebraic stacks, then
the relative inertia morphism `forget f : relativeInertia f ⟶ X` is flat and
locally of finite presentation. -/
@[stacks 0CPR]
theorem forget_flat_locallyOfFinitePresentation {S : Scheme.{u}}
    {X Y : GroupoidsOver S} [AlgebraicStack X] [AlgebraicStack Y]
    (f : X ⟶ Y) [Gerbe f] :
    Flat (forget.{u + 1, u, u, u + 1} f) ∧
      LocallyOfFinitePresentation (forget.{u + 1, u, u, u + 1} f) :=
  sorry

/-- The relative inertia morphism of a gerbe of algebraic stacks is flat. -/
instance instFlat_forget {S : Scheme.{u}} {X Y : GroupoidsOver S}
    [AlgebraicStack X] [AlgebraicStack Y] (f : X ⟶ Y) [Gerbe f] :
    Flat (forget.{u + 1, u, u, u + 1} f) :=
  sorry

/-- The relative inertia morphism of a gerbe of algebraic stacks is locally of
finite presentation. -/
instance instLocallyOfFinitePresentation_forget {S : Scheme.{u}}
    {X Y : GroupoidsOver S} [AlgebraicStack X] [AlgebraicStack Y]
    (f : X ⟶ Y) [Gerbe f] :
    LocallyOfFinitePresentation (forget.{u + 1, u, u, u + 1} f) :=
  sorry

end RelativeInertia

/-- Lemma 101.28.10 (2): if `f : X ⟶ Y` is a gerbe of algebraic stacks, then
the relative 2-diagonal `Hom.diagonal f : X ⟶ X ×_Y X` is surjective, flat,
and locally of finite presentation. -/
@[stacks 0CPR]
theorem diagonal_surjective_flat_locallyOfFinitePresentation
    {S : Scheme.{u}} {X Y : GroupoidsOver S}
    [AlgebraicStack X] [AlgebraicStack Y] (f : X ⟶ Y) [Gerbe f] :
    Surjective (Hom.diagonal.{u + 1, u, u + 1} f) ∧
      Flat (Hom.diagonal.{u + 1, u, u + 1} f) ∧
        LocallyOfFinitePresentation (Hom.diagonal.{u + 1, u, u + 1} f) :=
  sorry

namespace Surjective

/-- The relative 2-diagonal of a gerbe of algebraic stacks is surjective. -/
instance diagonal_of_gerbe {S : Scheme.{u}} {X Y : GroupoidsOver S}
    [AlgebraicStack X] [AlgebraicStack Y] (f : X ⟶ Y) [Gerbe f] :
    Surjective (Hom.diagonal.{u + 1, u, u + 1} f) :=
  sorry

end Surjective

namespace Flat

/-- The relative 2-diagonal of a gerbe of algebraic stacks is flat. -/
instance diagonal_of_gerbe {S : Scheme.{u}} {X Y : GroupoidsOver S}
    [AlgebraicStack X] [AlgebraicStack Y] (f : X ⟶ Y) [Gerbe f] :
    Flat (Hom.diagonal.{u + 1, u, u + 1} f) :=
  sorry

end Flat

namespace LocallyOfFinitePresentation

/-- The relative 2-diagonal of a gerbe of algebraic stacks is locally of finite
presentation. -/
instance diagonal_of_gerbe {S : Scheme.{u}} {X Y : GroupoidsOver S}
    [AlgebraicStack X] [AlgebraicStack Y] (f : X ⟶ Y) [Gerbe f] :
    LocallyOfFinitePresentation (Hom.diagonal.{u + 1, u, u + 1} f) :=
  sorry

end LocallyOfFinitePresentation

/-- Lemma 101.28.10 (3): if `f : X ⟶ Y` is a gerbe of algebraic stacks, then
for algebraic spaces `T1`, `T2` and maps `x1 : T1.toGroupoids ⟶ X`,
`x2 : T2.toGroupoids ⟶ X`, the comparison `fibreProductComparison f x1 x2`
from `T1 ×_X T2` to `T1 ×_Y T2` is surjective, flat, and locally of finite
presentation. -/
@[stacks 0CPR]
theorem fibreProductComparison_of_gerbe {S : Scheme.{u}}
    {X Y : GroupoidsOver S} [AlgebraicStack X] [AlgebraicStack Y]
    (f : X ⟶ Y) [Gerbe f] {T1 T2 : AlgebraicSpace S}
    (x1 : T1.toGroupoids ⟶ X) (x2 : T2.toGroupoids ⟶ X) :
    Surjective (fibreProductComparison f x1 x2) ∧
      Flat (fibreProductComparison f x1 x2) ∧
        LocallyOfFinitePresentation (fibreProductComparison f x1 x2) :=
  sorry

namespace Surjective

/-- The fibre-product comparison of a gerbe of algebraic stacks is surjective. -/
instance fibreProductComparison_of_gerbe {S : Scheme.{u}}
    {X Y : GroupoidsOver S} [AlgebraicStack X] [AlgebraicStack Y]
    (f : X ⟶ Y) [Gerbe f] {T1 T2 : AlgebraicSpace S}
    (x1 : T1.toGroupoids ⟶ X) (x2 : T2.toGroupoids ⟶ X) :
    Surjective (fibreProductComparison f x1 x2) :=
  sorry

end Surjective

namespace Flat

/-- The fibre-product comparison of a gerbe of algebraic stacks is flat. -/
instance fibreProductComparison_of_gerbe {S : Scheme.{u}}
    {X Y : GroupoidsOver S} [AlgebraicStack X] [AlgebraicStack Y]
    (f : X ⟶ Y) [Gerbe f] {T1 T2 : AlgebraicSpace S}
    (x1 : T1.toGroupoids ⟶ X) (x2 : T2.toGroupoids ⟶ X) :
    Flat (fibreProductComparison f x1 x2) :=
  sorry

end Flat

namespace LocallyOfFinitePresentation

/-- The fibre-product comparison of a gerbe of algebraic stacks is locally of
finite presentation. -/
instance fibreProductComparison_of_gerbe {S : Scheme.{u}}
    {X Y : GroupoidsOver S} [AlgebraicStack X] [AlgebraicStack Y]
    (f : X ⟶ Y) [Gerbe f] {T1 T2 : AlgebraicSpace S}
    (x1 : T1.toGroupoids ⟶ X) (x2 : T2.toGroupoids ⟶ X) :
    LocallyOfFinitePresentation (fibreProductComparison f x1 x2) :=
  sorry

end LocallyOfFinitePresentation

/-- Lemma 101.28.10 (4): if `f : X ⟶ Y` is a gerbe of algebraic stacks, then
for an algebraic space `T` and maps `x1, x2 : T.toGroupoids ⟶ X`, the
comparison `isomComparison f x1 x2` from `Isom_X(x1, x2)` to
`Isom_Y(x1 ≫ f, x2 ≫ f)` is surjective, flat, and locally of finite
presentation as a morphism of algebraic spaces. -/
@[stacks 0CPR]
theorem isomComparison_of_gerbe {S : Scheme.{u}} {X Y : GroupoidsOver S}
    [AlgebraicStack X] [AlgebraicStack Y] (f : X ⟶ Y) [Gerbe f]
    {T : AlgebraicSpace S} (x1 x2 : T.toGroupoids ⟶ X) :
    Groupoids.Hom.has (@AlgebraicSpace.Surjective S) (isomComparison f x1 x2) ∧
      Groupoids.Hom.has (@AlgebraicSpace.Flat S) (isomComparison f x1 x2) ∧
        Groupoids.Hom.has (@AlgebraicSpace.LocallyOfFinitePresentation S)
          (isomComparison f x1 x2) :=
  sorry

end AlgebraicGeometry.AlgebraicStack
