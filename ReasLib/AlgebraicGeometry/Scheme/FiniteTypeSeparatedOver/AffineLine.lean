/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.AlgebraicGeometry.AffineSpace.MorphismProperties
public import ReasLib.AlgebraicGeometry.Scheme.FiniteTypeSeparatedOver
public import ReasLib.AlgebraicGeometry.Scheme.Morphism.FiniteType.Operations

@[expose] public section

open CategoryTheory
open scoped AlgebraicGeometry

noncomputable section

universe u

namespace AlgebraicGeometry.Scheme.FiniteTypeSeparatedOver

variable {S : Scheme.{u}} [IsNoetherian S]

/-- The composite structure morphism of the affine line over an object of
`FiniteTypeSeparatedOver S` is separated and of finite type. -/
theorem affineLineCondition (Y : FiniteTypeSeparatedOver S) :
    IsSeparated
        ((𝔸(ULift (Fin 1); Y.obj.left) ↘ Y.obj.left) ≫ Y.obj.hom) ∧
      Hom.FiniteType
        ((𝔸(ULift (Fin 1); Y.obj.left) ↘ Y.obj.left) ≫ Y.obj.hom) := sorry

/-- The affine line over `Y`, regarded as an object of `FiniteTypeSeparatedOver S`. -/
noncomputable def affineLine (Y : FiniteTypeSeparatedOver S) :
    FiniteTypeSeparatedOver S :=
  ⟨Over.mk ((𝔸(ULift (Fin 1); Y.obj.left) ↘ Y.obj.left) ≫ Y.obj.hom),
    affineLineCondition Y⟩

/-- The underlying object over `S` of `affineLine Y`. -/
theorem affineLine_obj (Y : FiniteTypeSeparatedOver S) :
    (affineLine Y).obj =
      Over.mk ((𝔸(ULift (Fin 1); Y.obj.left) ↘ Y.obj.left) ≫ Y.obj.hom) := sorry

/-- The affine-line projection commutes with the structure morphisms to `S`. -/
theorem affineLineProjection_over (Y : FiniteTypeSeparatedOver S) :
    (𝔸(ULift (Fin 1); Y.obj.left) ↘ Y.obj.left) ≫ Y.obj.hom =
      (affineLine Y).obj.hom := sorry

/-- The projection from the affine line over `Y` to `Y` in
`FiniteTypeSeparatedOver S`. -/
def affineLineProjection (Y : FiniteTypeSeparatedOver S) : affineLine Y ⟶ Y :=
  ObjectProperty.homMk
    (Over.homMk (𝔸(ULift (Fin 1); Y.obj.left) ↘ Y.obj.left)
      (affineLineProjection_over Y))

/-- The underlying scheme morphism of `affineLineProjection Y` is the standard
affine-line projection. -/
theorem affineLineProjection_hom (Y : FiniteTypeSeparatedOver S) :
    (affineLineProjection Y).hom.left =
      (𝔸(ULift (Fin 1); Y.obj.left) ↘ Y.obj.left) := sorry

/-- The affine-line projection is flat. -/
instance affineLineProjection_flat (Y : FiniteTypeSeparatedOver S) :
    Flat (affineLineProjection Y).hom.left := sorry

end AlgebraicGeometry.Scheme.FiniteTypeSeparatedOver
