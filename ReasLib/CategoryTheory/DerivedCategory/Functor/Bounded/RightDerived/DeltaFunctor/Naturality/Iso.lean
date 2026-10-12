/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import ReasLib.CategoryTheory.DerivedCategory.Functor.Bounded.RightDerived.DeltaFunctor.Naturality
public import Mathlib.Tactic.CrossRefAttribute

@[expose] public section

/-!
# Model Isomorphisms of Bounded-Below Right-Derived Delta Functors

A shift-compatible isomorphism of bounded-below right-derived models induces
isomorphisms of both their pretriangulated and cohomological delta functors.
-/

open CategoryTheory
open scoped CategoryTheory

noncomputable section

universe w vA vB uA uB

namespace CategoryTheory.Functor.RightDerived

variable {A : Type uA} {B : Type uB}
  [Category.{vA} A] [Category.{vB} B]
  [Abelian A] [Abelian B]
  [HasDerivedCategory.{w} A] [HasDerivedCategory.{w} B]

namespace delta

/-- The maps induced by the two directions of a model isomorphism are
inverse on right-derived delta functors. -/
theorem mapIso_hom_inv_id
    {RF RG : DerivedCategory.Plus A ⥤ DerivedCategory.Plus B}
    [RF.CommShift ℤ] [RF.IsTriangulated]
    [RG.CommShift ℤ] [RG.IsTriangulated]
    (e : RF ≅ RG) [NatTrans.CommShift e.hom ℤ] :
    map e.hom ≫ map e.inv = 𝟙 (RightDerived.delta RF) := sorry

/-- The maps induced by the inverse and forward directions of a model
isomorphism are inverse on right-derived delta functors. -/
theorem mapIso_inv_hom_id
    {RF RG : DerivedCategory.Plus A ⥤ DerivedCategory.Plus B}
    [RF.CommShift ℤ] [RF.IsTriangulated]
    [RG.CommShift ℤ] [RG.IsTriangulated]
    (e : RF ≅ RG) [NatTrans.CommShift e.hom ℤ] :
    map e.inv ≫ map e.hom = 𝟙 (RightDerived.delta RG) := sorry

/-- A shift-compatible isomorphism of bounded-below right-derived models
induces an isomorphism of their pretriangulated delta functors. -/
@[stacks 05TE "isomorphism of bounded-below right-derived delta functors"]
noncomputable def mapIso
    {RF RG : DerivedCategory.Plus A ⥤ DerivedCategory.Plus B}
    [RF.CommShift ℤ] [RF.IsTriangulated]
    [RG.CommShift ℤ] [RG.IsTriangulated]
    (e : RF ≅ RG) [NatTrans.CommShift e.hom ℤ] :
    RightDerived.delta RF ≅ RightDerived.delta RG where
  hom := map e.hom
  inv := map e.inv
  hom_inv_id := mapIso_hom_inv_id e
  inv_hom_id := mapIso_inv_hom_id e

/-- The forward morphism of `mapIso` is induced by the forward model
transformation. -/
@[simp]
theorem mapIso_hom
    {RF RG : DerivedCategory.Plus A ⥤ DerivedCategory.Plus B}
    [RF.CommShift ℤ] [RF.IsTriangulated]
    [RG.CommShift ℤ] [RG.IsTriangulated]
    (e : RF ≅ RG) [NatTrans.CommShift e.hom ℤ] :
    (mapIso e).hom = map e.hom := sorry

/-- The inverse morphism of `mapIso` is induced by the inverse model
transformation. -/
@[simp]
theorem mapIso_inv
    {RF RG : DerivedCategory.Plus A ⥤ DerivedCategory.Plus B}
    [RF.CommShift ℤ] [RF.IsTriangulated]
    [RG.CommShift ℤ] [RG.IsTriangulated]
    (e : RF ≅ RG) [NatTrans.CommShift e.hom ℤ] :
    (mapIso e).inv = map e.inv := sorry

end delta

namespace cohomological

/-- A shift-compatible isomorphism of bounded-below right-derived models
induces an isomorphism of their cohomological delta functors. -/
@[stacks 05TE "isomorphism of bounded-below right-derived cohomological delta functors"]
noncomputable def mapIso
    {RF RG : DerivedCategory.Plus A ⥤ DerivedCategory.Plus B}
    [RF.CommShift ℤ] [RF.IsTriangulated]
    [RG.CommShift ℤ] [RG.IsTriangulated]
    (e : RF ≅ RG) [NatTrans.CommShift e.hom ℤ] :
    RightDerived.cohomological RF ≅ RightDerived.cohomological RG :=
  DeltaFunctor.toCohomologicalDeltaFunctor.mapIso
    (DerivedCategory.homologyFunctor B 0) (delta.mapIso e)
    (RightDerived.delta_hneg RF) (RightDerived.delta_hneg RG)

/-- The forward morphism of the cohomological model isomorphism is
cohomological naturality for the forward model transformation. -/
@[simp]
theorem mapIso_hom
    {RF RG : DerivedCategory.Plus A ⥤ DerivedCategory.Plus B}
    [RF.CommShift ℤ] [RF.IsTriangulated]
    [RG.CommShift ℤ] [RG.IsTriangulated]
    (e : RF ≅ RG) [NatTrans.CommShift e.hom ℤ] :
    (mapIso e).hom = map e.hom := sorry

/-- The inverse morphism of the cohomological model isomorphism is
cohomological naturality for the inverse model transformation. -/
@[simp]
theorem mapIso_inv
    {RF RG : DerivedCategory.Plus A ⥤ DerivedCategory.Plus B}
    [RF.CommShift ℤ] [RF.IsTriangulated]
    [RG.CommShift ℤ] [RG.IsTriangulated]
    (e : RF ≅ RG) [NatTrans.CommShift e.hom ℤ] :
    (mapIso e).inv = map e.inv := sorry

end cohomological

end CategoryTheory.Functor.RightDerived
