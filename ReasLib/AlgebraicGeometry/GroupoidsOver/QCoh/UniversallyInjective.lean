/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.AlgebraicGeometry.GroupoidsOver.QCoh.AffineTensor
public import ReasLib.LinearAlgebra.UniversallyInjective
public import ReasLib.AlgebraicGeometry.AlgebraicStack.Noetherian
public import ReasLib.AlgebraicGeometry.AlgebraicStack.Flat
public import ReasLib.AlgebraicGeometry.AlgebraicStack.Surjective

/-!
# Universal injectivity of evaluated pushforward coefficient maps

A symmetric monoidal functor gives a canonical coefficient linear map into an
evaluated pushforward of the structure module. For a Noetherian algebraic stack
with affine diagonal, a right exact such functor preserving direct sums makes
this map universally injective for a surjective flat morphism from an affine scheme.
-/

@[expose] public section

open AlgebraicGeometry AlgebraicGeometry.AlgebraicStack CategoryTheory
open CategoryTheory.Limits
open FiberedCategoryOver.Groupoids
open scoped Bicategory TensorProduct

noncomputable section

universe u

namespace AlgebraicGeometry.GroupoidsOver.QCoh

/-- The canonical coefficient linear map sends a scalar to its multiple of the
evaluated pushforward unit. -/
def algebraLinearMap {S : Scheme.{u}} {X : GroupoidsOver S} [AlgebraicStack X]
    {B : Type u} [CommRing B] (F : QCoh X ⥤ ModuleCat.{u} B) [F.Braided]
    {Y : GroupoidsOver S} [AlgebraicStack Y] (g : Y ⟶ X)
    [AlgebraicStack.QuasiCompact g] [AlgebraicStack.QuasiSeparated g] :
    B →ₗ[B] (algebraModule F g : Type u) :=
  LinearMap.toSpanSingleton B (algebraModule F g : Type u)
    (algebraOne F (tensorFunctorStructureSheafIso F) g)

/-- The coefficient linear map sends a scalar to its multiple of the image of one. -/
theorem algebraLinearMap_apply {S : Scheme.{u}} {X : GroupoidsOver S}
    [AlgebraicStack X] {B : Type u} [CommRing B]
    (F : QCoh X ⥤ ModuleCat.{u} B) [F.Braided]
    {Y : GroupoidsOver S} [AlgebraicStack Y] (g : Y ⟶ X)
    [AlgebraicStack.QuasiCompact g] [AlgebraicStack.QuasiSeparated g]
    (b : B) :
    algebraLinearMap F g b = b • algebraLinearMap F g 1 :=
  sorry

/-- The coefficient linear map sends one to the canonical evaluated pushforward unit. -/
theorem algebraLinearMap_one {S : Scheme.{u}} {X : GroupoidsOver S}
    [AlgebraicStack X] {B : Type u} [CommRing B]
    (F : QCoh X ⥤ ModuleCat.{u} B) [F.Braided]
    {Y : GroupoidsOver S} [AlgebraicStack Y] (g : Y ⟶ X)
    [AlgebraicStack.QuasiCompact g] [AlgebraicStack.QuasiSeparated g] :
    algebraLinearMap F g 1 = algebraOne F (tensorFunctorStructureSheafIso F) g :=
  sorry

/-- A right exact symmetric monoidal functor preserving direct sums gives a
universally injective coefficient map for a surjective flat morphism from an
affine scheme to a Noetherian algebraic stack with affine diagonal. -/
@[stacks 0GRL]
theorem algebraMap_universallyInjective
    {S : Scheme.{u}} {X : GroupoidsOver S} [AlgebraicStack X]
    [AlgebraicStack.IsNoetherian X]
    [Groupoids.Hom.Affine (diagonal.{u + 1, u, u + 1} X)]
    {B : Type u} [CommRing B]
    (F : QCoh X ⥤ ModuleCat.{u} B) [F.Braided]
    [PreservesFiniteColimits F]
    [∀ J : Type u, PreservesColimitsOfShape (Discrete J) F]
    {U : Over S} [IsAffine U.left]
    (g : GroupoidsOver.slice U ⟶ X)
    [AlgebraicStack.QuasiCompact g] [AlgebraicStack.QuasiSeparated g]
    [AlgebraicStack.Surjective g] [AlgebraicStack.Flat g] :
    LinearMap.UniversallyInjective.{u, u, u, u} (algebraLinearMap F g) :=
  sorry

end AlgebraicGeometry.GroupoidsOver.QCoh
