/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.AlgebraicGeometry.AlgebraicStack.Gerbe
public import ReasLib.AlgebraicGeometry.AlgebraicStack.Surjective
public import ReasLib.AlgebraicGeometry.AlgebraicStack.Flat
public import ReasLib.AlgebraicGeometry.AlgebraicStack.LocallyOfFinitePresentation
public import ReasLib.AlgebraicGeometry.AlgebraicStack.TwoFibreProduct
public import ReasLib.AlgebraicGeometry.AlgebraicStack.Inertia
public import ReasLib.AlgebraicGeometry.AlgebraicStack.Isom.Comparison

/-!
# Fppf properties of gerbe morphisms

Gerbe morphisms of algebraic stacks are surjective, flat, and locally of finite
presentation.
-/

@[expose] public section

open CategoryTheory AlgebraicGeometry FiberedCategoryOver.Groupoids
open scoped Bicategory

universe u

namespace AlgebraicGeometry.AlgebraicStack

/-- A morphism of algebraic stacks makes its source a gerbe over its target
if and only if both the morphism and its relative 2-diagonal are surjective,
flat, and locally of finite presentation. -/
theorem gerbe_iff_surjective_flat_locallyOfFinitePresentation_diagonal
    {S : Scheme.{u}} {X Y : GroupoidsOver S}
    [AlgebraicStack X] [AlgebraicStack Y] (f : X ⟶ Y) :
    Gerbe f ↔
      Surjective f ∧ Flat f ∧ LocallyOfFinitePresentation f ∧
        Surjective (Hom.diagonal.{u + 1, u, u + 1} f) ∧
          Flat (Hom.diagonal.{u + 1, u, u + 1} f) ∧
            LocallyOfFinitePresentation (Hom.diagonal.{u + 1, u, u + 1} f) :=
  sorry

namespace Surjective

/-- A gerbe morphism of algebraic stacks is surjective. -/
instance of_gerbe {S : Scheme.{u}} {X Y : GroupoidsOver S}
    [AlgebraicStack X] [AlgebraicStack Y] (f : X ⟶ Y) [Gerbe f] :
    Surjective f :=
  ((gerbe_iff_surjective_flat_locallyOfFinitePresentation_diagonal f).mp
    inferInstance).1

end Surjective

namespace Flat

/-- A gerbe morphism of algebraic stacks is flat. -/
instance of_gerbe {S : Scheme.{u}} {X Y : GroupoidsOver S}
    [AlgebraicStack X] [AlgebraicStack Y] (f : X ⟶ Y) [Gerbe f] :
    Flat f :=
  ((gerbe_iff_surjective_flat_locallyOfFinitePresentation_diagonal f).mp
    inferInstance).2.1

end Flat

namespace LocallyOfFinitePresentation

/-- A gerbe morphism of algebraic stacks is locally of finite presentation. -/
instance of_gerbe {S : Scheme.{u}} {X Y : GroupoidsOver S}
    [AlgebraicStack X] [AlgebraicStack Y] (f : X ⟶ Y) [Gerbe f] :
    LocallyOfFinitePresentation f :=
  ((gerbe_iff_surjective_flat_locallyOfFinitePresentation_diagonal f).mp
    inferInstance).2.2.1

end LocallyOfFinitePresentation

/-- A morphism of algebraic stacks that is surjective, flat, and locally of
finite presentation, and whose relative 2-diagonal is likewise surjective,
flat, and locally of finite presentation, is a gerbe over its target. -/
instance instGerbe_of_surjective_flat_locallyOfFinitePresentation_diagonal
    {S : Scheme.{u}} {X Y : GroupoidsOver S}
    [AlgebraicStack X] [AlgebraicStack Y] (f : X ⟶ Y)
    [Surjective f] [Flat f] [LocallyOfFinitePresentation f]
    [Surjective (Hom.diagonal.{u + 1, u, u + 1} f)]
    [Flat (Hom.diagonal.{u + 1, u, u + 1} f)]
    [LocallyOfFinitePresentation (Hom.diagonal.{u + 1, u, u + 1} f)] :
    Gerbe f :=
  (gerbe_iff_surjective_flat_locallyOfFinitePresentation_diagonal f).mpr
    ⟨inferInstance, inferInstance, inferInstance,
      inferInstance, inferInstance, inferInstance⟩

namespace RelativeInertia

open FiberedCategoryOver.Groupoids.RelativeInertia (forget)

/-- The relative inertia projection of a gerbe morphism of algebraic stacks is
flat and locally of finite presentation. -/
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
  (forget_flat_locallyOfFinitePresentation f).1

/-- The relative inertia morphism of a gerbe of algebraic stacks is locally of
finite presentation. -/
instance instLocallyOfFinitePresentation_forget {S : Scheme.{u}}
    {X Y : GroupoidsOver S} [AlgebraicStack X] [AlgebraicStack Y]
    (f : X ⟶ Y) [Gerbe f] :
    LocallyOfFinitePresentation (forget.{u + 1, u, u, u + 1} f) :=
  (forget_flat_locallyOfFinitePresentation f).2

end RelativeInertia

/-- The relative 2-diagonal of a gerbe morphism of algebraic stacks is
surjective, flat, and locally of finite presentation. -/
@[stacks 0CPR]
theorem diagonal_surjective_flat_locallyOfFinitePresentation
    {S : Scheme.{u}} {X Y : GroupoidsOver S}
    [AlgebraicStack X] [AlgebraicStack Y] (f : X ⟶ Y) [Gerbe f] :
    Surjective (Hom.diagonal.{u + 1, u, u + 1} f) ∧
      Flat (Hom.diagonal.{u + 1, u, u + 1} f) ∧
        LocallyOfFinitePresentation (Hom.diagonal.{u + 1, u, u + 1} f) :=
  ((gerbe_iff_surjective_flat_locallyOfFinitePresentation_diagonal f).mp
    inferInstance).2.2.2

namespace Surjective

/-- The relative 2-diagonal of a gerbe of algebraic stacks is surjective. -/
instance diagonal_of_gerbe {S : Scheme.{u}} {X Y : GroupoidsOver S}
    [AlgebraicStack X] [AlgebraicStack Y] (f : X ⟶ Y) [Gerbe f] :
    Surjective (Hom.diagonal.{u + 1, u, u + 1} f) :=
  (diagonal_surjective_flat_locallyOfFinitePresentation f).1

end Surjective

namespace Flat

/-- The relative 2-diagonal of a gerbe of algebraic stacks is flat. -/
instance diagonal_of_gerbe {S : Scheme.{u}} {X Y : GroupoidsOver S}
    [AlgebraicStack X] [AlgebraicStack Y] (f : X ⟶ Y) [Gerbe f] :
    Flat (Hom.diagonal.{u + 1, u, u + 1} f) :=
  (diagonal_surjective_flat_locallyOfFinitePresentation f).2.1

end Flat

namespace LocallyOfFinitePresentation

/-- The relative 2-diagonal of a gerbe of algebraic stacks is locally of finite
presentation. -/
instance diagonal_of_gerbe {S : Scheme.{u}} {X Y : GroupoidsOver S}
    [AlgebraicStack X] [AlgebraicStack Y] (f : X ⟶ Y) [Gerbe f] :
    LocallyOfFinitePresentation (Hom.diagonal.{u + 1, u, u + 1} f) :=
  (diagonal_surjective_flat_locallyOfFinitePresentation f).2.2

end LocallyOfFinitePresentation

/-- For algebraic spaces mapping to the source of a gerbe morphism of
algebraic stacks, postcomposition induces a surjective, flat, locally finitely
presented map on their two-fibre products. -/
@[stacks 0CPR]
theorem fibreProductComparison_of_gerbe {S : Scheme.{u}}
    {X Y : GroupoidsOver S} [AlgebraicStack X] [AlgebraicStack Y]
    (f : X ⟶ Y) [Gerbe f] {T1 T2 : AlgebraicSpace S}
    (x1 : T1.toGroupoids ⟶ X) (x2 : T2.toGroupoids ⟶ X) :
    Surjective (TwoFibreProduct.mapPostcompose.{u + 1, u, u + 1, u} x1 x2 f) ∧
      Flat (TwoFibreProduct.mapPostcompose.{u + 1, u, u + 1, u} x1 x2 f) ∧
        LocallyOfFinitePresentation (TwoFibreProduct.mapPostcompose.{u + 1, u, u + 1, u} x1 x2 f) :=
  sorry

namespace Surjective

/-- The fibre-product comparison of a gerbe of algebraic stacks is surjective. -/
instance fibreProductComparison_of_gerbe {S : Scheme.{u}}
    {X Y : GroupoidsOver S} [AlgebraicStack X] [AlgebraicStack Y]
    (f : X ⟶ Y) [Gerbe f] {T1 T2 : AlgebraicSpace S}
    (x1 : T1.toGroupoids ⟶ X) (x2 : T2.toGroupoids ⟶ X) :
    Surjective (TwoFibreProduct.mapPostcompose.{u + 1, u, u + 1, u} x1 x2 f) :=
  (AlgebraicStack.fibreProductComparison_of_gerbe f x1 x2).1

end Surjective

namespace Flat

/-- The fibre-product comparison of a gerbe of algebraic stacks is flat. -/
instance fibreProductComparison_of_gerbe {S : Scheme.{u}}
    {X Y : GroupoidsOver S} [AlgebraicStack X] [AlgebraicStack Y]
    (f : X ⟶ Y) [Gerbe f] {T1 T2 : AlgebraicSpace S}
    (x1 : T1.toGroupoids ⟶ X) (x2 : T2.toGroupoids ⟶ X) :
    Flat (TwoFibreProduct.mapPostcompose.{u + 1, u, u + 1, u} x1 x2 f) :=
  (AlgebraicStack.fibreProductComparison_of_gerbe f x1 x2).2.1

end Flat

namespace LocallyOfFinitePresentation

/-- The fibre-product comparison of a gerbe of algebraic stacks is locally of
finite presentation. -/
instance fibreProductComparison_of_gerbe {S : Scheme.{u}}
    {X Y : GroupoidsOver S} [AlgebraicStack X] [AlgebraicStack Y]
    (f : X ⟶ Y) [Gerbe f] {T1 T2 : AlgebraicSpace S}
    (x1 : T1.toGroupoids ⟶ X) (x2 : T2.toGroupoids ⟶ X) :
    LocallyOfFinitePresentation (TwoFibreProduct.mapPostcompose.{u + 1, u, u + 1, u} x1 x2 f) :=
  (AlgebraicStack.fibreProductComparison_of_gerbe f x1 x2).2.2

end LocallyOfFinitePresentation

/-- For two maps from an algebraic space to the source of a gerbe morphism
of algebraic stacks, the canonical comparison of Isom spaces is surjective,
flat, and locally of finite presentation. -/
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
