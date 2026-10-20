/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.CategoryTheory.Fibered.TwoFibreProduct.Postcompose
public import ReasLib.AlgebraicGeometry.AlgebraicStack.Separation
public import ReasLib.AlgebraicGeometry.GroupoidsOver.LocallyOfFiniteType

/-!
# Comparison of two-fibre products of algebraic stacks

Postcomposing two morphisms of algebraic stacks induces a representable,
locally finite type comparison between their two-fibre products. Properties of
the relative diagonal control the separation and finiteness of this comparison.
-/

@[expose] public section

open CategoryTheory AlgebraicGeometry
open Bicategory
open FiberedCategoryOver.Groupoids
open scoped Bicategory

universe u

namespace AlgebraicGeometry.Groupoids.Hom.LocallyOfFiniteType

/-- The comparison between two-fibre products induced by postcomposition of
morphisms of algebraic stacks is representable by algebraic spaces and locally
of finite type. -/
instance mapPostcompose {S : Scheme.{u}} {X Y Z T : GroupoidsOver S}
    [AlgebraicStack X] [AlgebraicStack Y] [AlgebraicStack Z] [AlgebraicStack T]
    (f : X ⟶ Z) (g : Y ⟶ Z) (h : Z ⟶ T) :
    LocallyOfFiniteType (TwoFibreProduct.mapPostcompose.{u + 1, u, u + 1, u} f g h) :=
  sorry

end AlgebraicGeometry.Groupoids.Hom.LocallyOfFiniteType

namespace AlgebraicGeometry.AlgebraicStack

/-- The comparison between two-fibre products of algebraic stacks induced by
postcomposition is representable by algebraic spaces. -/
theorem relativelyRepresentable_mapPostcompose {S : Scheme.{u}}
    {X Y Z T : GroupoidsOver S} [AlgebraicStack X] [AlgebraicStack Y]
    [AlgebraicStack Z] [AlgebraicStack T] (f : X ⟶ Z) (g : Y ⟶ Z)
    (h : Z ⟶ T) :
    relativelyRepresentableByAlgebraicSpaces (TwoFibreProduct.mapPostcompose.{u + 1, u, u + 1, u} f g h) :=
  Groupoids.Hom.LocallyOfFiniteType.relativelyRepresentable
    (TwoFibreProduct.mapPostcompose.{u + 1, u, u + 1, u} f g h)

/-- The comparison between two-fibre products of algebraic stacks is
quasi-separated if the relative diagonal of the postcomposing morphism is
quasi-separated. -/
theorem mapPostcompose_quasiSeparated {S : Scheme.{u}} {X Y Z T : GroupoidsOver S}
    [AlgebraicStack X] [AlgebraicStack Y] [AlgebraicStack Z] [AlgebraicStack T]
    (f : X ⟶ Z) (g : Y ⟶ Z) (h : Z ⟶ T)
    (h_quasiSeparated :
      Groupoids.Hom.has (@AlgebraicSpace.QuasiSeparated S)
        (Hom.diagonal.{u + 1, u, u + 1} h)) :
    Groupoids.Hom.has (@AlgebraicSpace.QuasiSeparated S) (TwoFibreProduct.mapPostcompose.{u + 1, u, u + 1, u} f g h) :=
  sorry

/-- The comparison between two-fibre products of algebraic stacks is
separated if the relative diagonal of the postcomposing morphism is separated. -/
theorem mapPostcompose_separated {S : Scheme.{u}} {X Y Z T : GroupoidsOver S}
    [AlgebraicStack X] [AlgebraicStack Y] [AlgebraicStack Z] [AlgebraicStack T]
    (f : X ⟶ Z) (g : Y ⟶ Z) (h : Z ⟶ T)
    (h_separated :
      Groupoids.Hom.has (@AlgebraicSpace.Separated S)
        (Hom.diagonal.{u + 1, u, u + 1} h)) :
    Groupoids.Hom.has (@AlgebraicSpace.Separated S) (TwoFibreProduct.mapPostcompose.{u + 1, u, u + 1, u} f g h) :=
  sorry

/-- The comparison between two-fibre products of algebraic stacks induced by
postcomposition with a DM morphism is unramified. -/
theorem mapPostcompose_unramified {S : Scheme.{u}} {X Y Z T : GroupoidsOver S}
    [AlgebraicStack X] [AlgebraicStack Y] [AlgebraicStack Z] [AlgebraicStack T]
    (f : X ⟶ Z) (g : Y ⟶ Z) (h : Z ⟶ T) [DM h] :
    Groupoids.Hom.has (@AlgebraicSpace.Unramified S) (TwoFibreProduct.mapPostcompose.{u + 1, u, u + 1, u} f g h) :=
  sorry

/-- The comparison between two-fibre products of algebraic stacks induced by
postcomposition with a quasi-DM morphism is locally quasi-finite. -/
theorem mapPostcompose_locallyQuasiFinite {S : Scheme.{u}} {X Y Z T : GroupoidsOver S}
    [AlgebraicStack X] [AlgebraicStack Y] [AlgebraicStack Z] [AlgebraicStack T]
    (f : X ⟶ Z) (g : Y ⟶ Z) (h : Z ⟶ T) [QuasiDM h] :
    Groupoids.Hom.has (@AlgebraicSpace.LocallyQuasiFinite S) (TwoFibreProduct.mapPostcompose.{u + 1, u, u + 1, u} f g h) :=
  sorry

/-- The comparison between two-fibre products of algebraic stacks induced by
postcomposition with a separated morphism is proper. -/
theorem mapPostcompose_proper {S : Scheme.{u}} {X Y Z T : GroupoidsOver S}
    [AlgebraicStack X] [AlgebraicStack Y] [AlgebraicStack Z] [AlgebraicStack T]
    (f : X ⟶ Z) (g : Y ⟶ Z) (h : Z ⟶ T) [Separated h] :
    Groupoids.Hom.has (@AlgebraicSpace.Proper S) (TwoFibreProduct.mapPostcompose.{u + 1, u, u + 1, u} f g h) :=
  sorry

/-- The comparison between two-fibre products of algebraic stacks induced by
postcomposition with a quasi-separated morphism is quasi-compact and
quasi-separated. -/
theorem mapPostcompose_quasiCompact_quasiSeparated {S : Scheme.{u}}
    {X Y Z T : GroupoidsOver S} [AlgebraicStack X] [AlgebraicStack Y]
    [AlgebraicStack Z] [AlgebraicStack T] (f : X ⟶ Z) (g : Y ⟶ Z)
    (h : Z ⟶ T) [QuasiSeparated h] :
    Groupoids.Hom.has (@AlgebraicSpace.QuasiCompact S) (TwoFibreProduct.mapPostcompose.{u + 1, u, u + 1, u} f g h) ∧
      Groupoids.Hom.has (@AlgebraicSpace.QuasiSeparated S) (TwoFibreProduct.mapPostcompose.{u + 1, u, u + 1, u} f g h) :=
  sorry

/-- The comparison between two-fibre products of algebraic stacks induced by
postcomposition with a quasi-separated morphism is quasi-compact. -/
theorem mapPostcompose_quasiCompact {S : Scheme.{u}} {X Y Z T : GroupoidsOver S}
    [AlgebraicStack X] [AlgebraicStack Y] [AlgebraicStack Z] [AlgebraicStack T]
    (f : X ⟶ Z) (g : Y ⟶ Z) (h : Z ⟶ T) [QuasiSeparated h] :
    Groupoids.Hom.has (@AlgebraicSpace.QuasiCompact S) (TwoFibreProduct.mapPostcompose.{u + 1, u, u + 1, u} f g h) :=
  (mapPostcompose_quasiCompact_quasiSeparated f g h).1

/-- The comparison between two-fibre products of algebraic stacks induced by
postcomposition with a quasi-separated morphism is quasi-separated. -/
theorem mapPostcompose_isQuasiSeparated {S : Scheme.{u}} {X Y Z T : GroupoidsOver S}
    [AlgebraicStack X] [AlgebraicStack Y] [AlgebraicStack Z] [AlgebraicStack T]
    (f : X ⟶ Z) (g : Y ⟶ Z) (h : Z ⟶ T) [QuasiSeparated h] :
    Groupoids.Hom.has (@AlgebraicSpace.QuasiSeparated S) (TwoFibreProduct.mapPostcompose.{u + 1, u, u + 1, u} f g h) :=
  (mapPostcompose_quasiCompact_quasiSeparated f g h).2

end AlgebraicGeometry.AlgebraicStack
