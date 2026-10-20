/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.AlgebraicGeometry.AlgebraicStack.PullbackComparison
public import ReasLib.AlgebraicGeometry.AlgebraicStack.Isom.Comparison
import StacksCheckRecall

/-!
# Fibre-product and Isom comparisons for separation axioms

For a separated, quasi-separated, quasi-DM, or DM morphism of algebraic
stacks, the fibre-product and Isom comparisons are respectively proper,
quasi-compact and quasi-separated, locally quasi-finite, or unramified.
The generic fibre-product statements apply in particular to algebraic-space
inputs through their canonical algebraic-stack instances.
-/

@[expose] public section

open CategoryTheory AlgebraicGeometry
open Bicategory
open scoped Bicategory

universe u

namespace AlgebraicGeometry.AlgebraicStack

/- Lemma 101.6.6. Postcomposition induces the stated separation and finiteness
properties on fibre products and on Isom objects of algebraic spaces. -/
@[stacks 0CPL] #check (AlgebraicGeometry.AlgebraicStack.mapPostcompose_proper :
    ∀ {S : Scheme.{u}} {X Y Z T : GroupoidsOver S}
    [AlgebraicStack X] [AlgebraicStack Y] [AlgebraicStack Z] [AlgebraicStack T]
    (f : X ⟶ Z) (g : Y ⟶ Z) (h : Z ⟶ T) [Separated h],
      Groupoids.Hom.has (@AlgebraicSpace.Proper S) (TwoFibreProduct.mapPostcompose.{u + 1, u, u + 1, u} f g h))

#check (AlgebraicGeometry.AlgebraicStack.mapPostcompose_quasiCompact_quasiSeparated :
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

#check (AlgebraicGeometry.AlgebraicStack.mapPostcompose_locallyQuasiFinite :
    ∀ {S : Scheme.{u}} {X Y Z T : GroupoidsOver S}
    [AlgebraicStack X] [AlgebraicStack Y] [AlgebraicStack Z] [AlgebraicStack T]
    (f : X ⟶ Z) (g : Y ⟶ Z) (h : Z ⟶ T) [QuasiDM h],
      Groupoids.Hom.has (@AlgebraicSpace.LocallyQuasiFinite S) (TwoFibreProduct.mapPostcompose.{u + 1, u, u + 1, u} f g h))

#check (AlgebraicGeometry.AlgebraicStack.mapPostcompose_unramified :
    ∀ {S : Scheme.{u}} {X Y Z T : GroupoidsOver S}
    [AlgebraicStack X] [AlgebraicStack Y] [AlgebraicStack Z] [AlgebraicStack T]
    (f : X ⟶ Z) (g : Y ⟶ Z) (h : Z ⟶ T) [DM h],
      Groupoids.Hom.has (@AlgebraicSpace.Unramified S) (TwoFibreProduct.mapPostcompose.{u + 1, u, u + 1, u} f g h))

#check (AlgebraicGeometry.AlgebraicStack.isomComparison_proper :
    ∀ {S : Scheme.{u}} {X Y : GroupoidsOver S}
    [AlgebraicStack X] [AlgebraicStack Y] (f : X ⟶ Y) [Separated f]
    {T : AlgebraicSpace S} (x1 x2 : T.toGroupoids ⟶ X),
      Groupoids.Hom.has (@AlgebraicSpace.Proper S) (isomComparison f x1 x2))

#check (AlgebraicGeometry.AlgebraicStack.isomComparison_quasiSeparated :
    ∀ {S : Scheme.{u}} {X Y : GroupoidsOver S}
    [AlgebraicStack X] [AlgebraicStack Y] (f : X ⟶ Y) [QuasiSeparated f]
    {T : AlgebraicSpace S} (x1 x2 : T.toGroupoids ⟶ X),
      Groupoids.Hom.has (@AlgebraicSpace.QuasiCompact S)
        (isomComparison f x1 x2) ∧
      Groupoids.Hom.has (@AlgebraicSpace.QuasiSeparated S)
        (isomComparison f x1 x2))

#check (AlgebraicGeometry.AlgebraicStack.isomComparison_quasiCompact :
    ∀ {S : Scheme.{u}} {X Y : GroupoidsOver S}
    [AlgebraicStack X] [AlgebraicStack Y] (f : X ⟶ Y) [QuasiSeparated f]
    {T : AlgebraicSpace S} (x1 x2 : T.toGroupoids ⟶ X),
      Groupoids.Hom.has (@AlgebraicSpace.QuasiCompact S)
      (isomComparison f x1 x2))

#check (AlgebraicGeometry.AlgebraicStack.isomComparison_isQuasiSeparated :
    ∀ {S : Scheme.{u}} {X Y : GroupoidsOver S}
    [AlgebraicStack X] [AlgebraicStack Y] (f : X ⟶ Y) [QuasiSeparated f]
    {T : AlgebraicSpace S} (x1 x2 : T.toGroupoids ⟶ X),
      Groupoids.Hom.has (@AlgebraicSpace.QuasiSeparated S)
      (isomComparison f x1 x2))

#check (AlgebraicGeometry.AlgebraicStack.isomComparison_locallyQuasiFinite :
    ∀ {S : Scheme.{u}}
    {X Y : GroupoidsOver S} [AlgebraicStack X] [AlgebraicStack Y] (f : X ⟶ Y)
    [QuasiDM f] {T : AlgebraicSpace S} (x1 x2 : T.toGroupoids ⟶ X),
      Groupoids.Hom.has (@AlgebraicSpace.LocallyQuasiFinite S)
      (isomComparison f x1 x2))

#check (AlgebraicGeometry.AlgebraicStack.isomComparison_unramified :
    ∀ {S : Scheme.{u}} {X Y : GroupoidsOver S}
    [AlgebraicStack X] [AlgebraicStack Y] (f : X ⟶ Y) [DM f]
    {T : AlgebraicSpace S} (x1 x2 : T.toGroupoids ⟶ X),
      Groupoids.Hom.has (@AlgebraicSpace.Unramified S)
      (isomComparison f x1 x2))

end AlgebraicGeometry.AlgebraicStack
