/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.AlgebraicGeometry.AlgebraicStack.PullbackComparison
import StacksCheckRecall

open CategoryTheory AlgebraicGeometry
open FiberedCategoryOver.Groupoids
open scoped Bicategory

universe u

namespace AlgebraicGeometry.AlgebraicStack

/- Lemma 101.4.7: the comparison of two-fibre products is representable by
algebraic spaces and locally of finite type, with separation and finiteness
properties inherited from the relative diagonal. -/
@[stacks 050H] #check (AlgebraicGeometry.Groupoids.Hom.LocallyOfFiniteType.mapPostcompose :
    ∀ {S : Scheme.{u}} {X Y Z T : GroupoidsOver S}
    [AlgebraicStack X] [AlgebraicStack Y] [AlgebraicStack Z] [AlgebraicStack T]
    (f : X ⟶ Z) (g : Y ⟶ Z) (h : Z ⟶ T),
    Groupoids.Hom.LocallyOfFiniteType (TwoFibreProduct.mapPostcompose.{u + 1, u, u + 1, u} f g h))

#check (AlgebraicGeometry.AlgebraicStack.relativelyRepresentable_mapPostcompose :
    ∀ {S : Scheme.{u}}
    {X Y Z T : GroupoidsOver S} [AlgebraicStack X] [AlgebraicStack Y]
    [AlgebraicStack Z] [AlgebraicStack T] (f : X ⟶ Z) (g : Y ⟶ Z)
    (h : Z ⟶ T),
    relativelyRepresentableByAlgebraicSpaces (TwoFibreProduct.mapPostcompose.{u + 1, u, u + 1, u} f g h))

@[stacks 050H] #check (AlgebraicGeometry.AlgebraicStack.mapPostcompose_quasiSeparated :
    ∀ {S : Scheme.{u}} {X Y Z T : GroupoidsOver S}
    [AlgebraicStack X] [AlgebraicStack Y] [AlgebraicStack Z] [AlgebraicStack T]
    (f : X ⟶ Z) (g : Y ⟶ Z) (h : Z ⟶ T)
    (h_quasiSeparated :
      Groupoids.Hom.has (@AlgebraicSpace.QuasiSeparated S)
        (Hom.diagonal.{u + 1, u, u + 1} h)),
    Groupoids.Hom.has (@AlgebraicSpace.QuasiSeparated S) (TwoFibreProduct.mapPostcompose.{u + 1, u, u + 1, u} f g h))

@[stacks 050H] #check (AlgebraicGeometry.AlgebraicStack.mapPostcompose_separated :
    ∀ {S : Scheme.{u}} {X Y Z T : GroupoidsOver S}
    [AlgebraicStack X] [AlgebraicStack Y] [AlgebraicStack Z] [AlgebraicStack T]
    (f : X ⟶ Z) (g : Y ⟶ Z) (h : Z ⟶ T)
    (h_separated :
      Groupoids.Hom.has (@AlgebraicSpace.Separated S)
        (Hom.diagonal.{u + 1, u, u + 1} h)),
    Groupoids.Hom.has (@AlgebraicSpace.Separated S) (TwoFibreProduct.mapPostcompose.{u + 1, u, u + 1, u} f g h))

@[stacks 050H] #check (AlgebraicGeometry.AlgebraicStack.mapPostcompose_unramified :
    ∀ {S : Scheme.{u}} {X Y Z T : GroupoidsOver S}
    [AlgebraicStack X] [AlgebraicStack Y] [AlgebraicStack Z] [AlgebraicStack T]
    (f : X ⟶ Z) (g : Y ⟶ Z) (h : Z ⟶ T) [DM h],
    Groupoids.Hom.has (@AlgebraicSpace.Unramified S) (TwoFibreProduct.mapPostcompose.{u + 1, u, u + 1, u} f g h))

@[stacks 050H] #check (AlgebraicGeometry.AlgebraicStack.mapPostcompose_locallyQuasiFinite :
    ∀ {S : Scheme.{u}} {X Y Z T : GroupoidsOver S}
    [AlgebraicStack X] [AlgebraicStack Y] [AlgebraicStack Z] [AlgebraicStack T]
    (f : X ⟶ Z) (g : Y ⟶ Z) (h : Z ⟶ T) [QuasiDM h],
    Groupoids.Hom.has (@AlgebraicSpace.LocallyQuasiFinite S) (TwoFibreProduct.mapPostcompose.{u + 1, u, u + 1, u} f g h))

@[stacks 050H] #check (AlgebraicGeometry.AlgebraicStack.mapPostcompose_proper :
    ∀ {S : Scheme.{u}} {X Y Z T : GroupoidsOver S}
    [AlgebraicStack X] [AlgebraicStack Y] [AlgebraicStack Z] [AlgebraicStack T]
    (f : X ⟶ Z) (g : Y ⟶ Z) (h : Z ⟶ T) [Separated h],
    Groupoids.Hom.has (@AlgebraicSpace.Proper S) (TwoFibreProduct.mapPostcompose.{u + 1, u, u + 1, u} f g h))

@[stacks 050H] #check (AlgebraicGeometry.AlgebraicStack.mapPostcompose_quasiCompact_quasiSeparated :
    ∀ {S : Scheme.{u}}
    {X Y Z T : GroupoidsOver S} [AlgebraicStack X] [AlgebraicStack Y]
    [AlgebraicStack Z] [AlgebraicStack T] (f : X ⟶ Z) (g : Y ⟶ Z)
    (h : Z ⟶ T) [QuasiSeparated h],
    Groupoids.Hom.has (@AlgebraicSpace.QuasiCompact S) (TwoFibreProduct.mapPostcompose.{u + 1, u, u + 1, u} f g h) ∧
      Groupoids.Hom.has (@AlgebraicSpace.QuasiSeparated S) (TwoFibreProduct.mapPostcompose.{u + 1, u, u + 1, u} f g h))

#check (AlgebraicGeometry.AlgebraicStack.mapPostcompose_quasiCompact :
    ∀ {S : Scheme.{u}} {X Y Z T : GroupoidsOver S}
    [AlgebraicStack X] [AlgebraicStack Y] [AlgebraicStack Z] [AlgebraicStack T]
    (f : X ⟶ Z) (g : Y ⟶ Z) (h : Z ⟶ T) [QuasiSeparated h],
    Groupoids.Hom.has (@AlgebraicSpace.QuasiCompact S) (TwoFibreProduct.mapPostcompose.{u + 1, u, u + 1, u} f g h))

#check (AlgebraicGeometry.AlgebraicStack.mapPostcompose_isQuasiSeparated :
    ∀ {S : Scheme.{u}} {X Y Z T : GroupoidsOver S}
    [AlgebraicStack X] [AlgebraicStack Y] [AlgebraicStack Z] [AlgebraicStack T]
    (f : X ⟶ Z) (g : Y ⟶ Z) (h : Z ⟶ T) [QuasiSeparated h],
    Groupoids.Hom.has (@AlgebraicSpace.QuasiSeparated S) (TwoFibreProduct.mapPostcompose.{u + 1, u, u + 1, u} f g h))

end AlgebraicGeometry.AlgebraicStack
