/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.CategoryTheory.Pretriangulated.DeltaFunctor.Composition
public import ReasLib.CategoryTheory.Pretriangulated.DeltaFunctor.Morphism
public import Mathlib.Tactic.CrossRefAttribute

@[expose] public section

/-!
# Functoriality of Composition of Delta Functors

Exact postcomposition and precomposition act on morphisms of delta functors.
This upgrades the object-level constructors in `Composition` to functors.
-/

open CategoryTheory.Pretriangulated

noncomputable section

universe vA vA' vD vD' uA uA' uD uD'

namespace CategoryTheory.DeltaFunctor

section Postcompose

variable {A : Type uA} [Category.{vA} A] [Abelian A]
variable {D : Type uD} [Category.{vD} D] [Limits.HasZeroObject D]
  [HasShift D ℤ] [Preadditive D]
  [∀ n : ℤ, (shiftFunctor D n).Additive] [Pretriangulated D]
variable {D' : Type uD'} [Category.{vD'} D'] [Limits.HasZeroObject D']
  [HasShift D' ℤ] [Preadditive D']
  [∀ n : ℤ, (shiftFunctor D' n).Additive] [Pretriangulated D']
variable (F : D ⥤ D') [F.CommShift ℤ] [F.IsTriangulated]

namespace postcomposeExactFunctor

/-- Exact postcomposition preserves compatibility with connecting maps. -/
@[stacks 0151 "naturality of exact postcomposition of delta functors"]
theorem map_comm {G G' : DeltaFunctor A D} (τ : G ⟶ G')
    {S : ShortComplex A} (hS : S.ShortExact) :
    CommSq ((Functor.whiskerRight τ.app F).app S.X₃)
      ((G.postcomposeExactFunctor F).δ hS)
      ((G'.postcomposeExactFunctor F).δ hS)
      (((Functor.whiskerRight τ.app F).app S.X₁)⟦(1 : ℤ)⟧') := by
  exact CommSq.vert_comp ((τ.comm hS).map F)
    (CommSq.mk (F.commShiftIso_hom_naturality (τ.app.app S.X₁) (1 : ℤ)))

/-- A morphism of delta functors can be postcomposed with an exact
triangulated functor. -/
@[stacks 0151 "map under exact postcomposition of delta functors"]
noncomputable def map {G G' : DeltaFunctor A D} (τ : G ⟶ G') :
    G.postcomposeExactFunctor F ⟶ G'.postcomposeExactFunctor F where
  app := Functor.whiskerRight τ.app F
  comm := fun {_} hS ↦ map_comm F τ hS

/-- Exact postcomposition sends identity delta-functor morphisms to identities. -/
@[simp]
theorem map_id (G : DeltaFunctor A D) :
    map F (𝟙 G) = 𝟙 (G.postcomposeExactFunctor F) := by
  apply Hom.ext
  apply NatTrans.ext
  funext X
  exact F.map_id (G.obj X)

/-- Exact postcomposition preserves composition of delta-functor morphisms. -/
@[simp]
theorem map_comp {G G' G'' : DeltaFunctor A D} (τ : G ⟶ G') (σ : G' ⟶ G'') :
    map F (τ ≫ σ) = map F τ ≫ map F σ := by
  apply Hom.ext
  apply NatTrans.ext
  funext X
  exact F.map_comp (τ.app.app X) (σ.app.app X)

/-- Exact postcomposition is a functor between categories of delta functors. -/
@[stacks 0151 "functorial exact postcomposition of delta functors"]
noncomputable def functor : DeltaFunctor A D ⥤ DeltaFunctor A D' where
  obj G := G.postcomposeExactFunctor F
  map τ := map F τ
  map_id := map_id F
  map_comp := map_comp F

/-- The object action of exact postcomposition is the object-level
constructor `postcomposeExactFunctor`. -/
@[simp]
theorem functor_obj (G : DeltaFunctor A D) :
    (functor F).obj G = G.postcomposeExactFunctor F := rfl

/-- The component of a postcomposed delta-functor morphism is obtained by
applying the exact functor. -/
@[simp]
theorem map_app {G G' : DeltaFunctor A D} (τ : G ⟶ G') (X : A) :
    (map F τ).app.app X = F.map (τ.app.app X) := rfl

end postcomposeExactFunctor

end Postcompose

section Precompose

variable {A : Type uA} [Category.{vA} A] [Abelian A]
variable {A' : Type uA'} [Category.{vA'} A'] [Abelian A']
variable {D : Type uD} [Category.{vD} D] [Limits.HasZeroObject D]
  [HasShift D ℤ] [Preadditive D]
  [∀ n : ℤ, (shiftFunctor D n).Additive] [Pretriangulated D]
variable (H : A' ⥤ₑ A)

namespace precomposeExactFunctor

/-- Exact precomposition preserves compatibility with connecting maps. -/
@[stacks 0151 "naturality of exact precomposition of delta functors"]
theorem map_comm {G G' : DeltaFunctor A D} (τ : G ⟶ G')
    {S : ShortComplex A'} (hS : S.ShortExact) :
    CommSq ((Functor.whiskerLeft H.obj τ.app).app S.X₃)
      ((G.precomposeExactFunctor H).δ hS)
      ((G'.precomposeExactFunctor H).δ hS)
      (((Functor.whiskerLeft H.obj τ.app).app S.X₁)⟦(1 : ℤ)⟧') := by
  exact τ.comm (hS.map_of_exact H.obj)

/-- A morphism of delta functors can be precomposed with an exact functor. -/
@[stacks 0151 "map under exact precomposition of delta functors"]
noncomputable def map {G G' : DeltaFunctor A D} (τ : G ⟶ G') :
    G.precomposeExactFunctor H ⟶ G'.precomposeExactFunctor H where
  app := Functor.whiskerLeft H.obj τ.app
  comm := fun {_} hS ↦ map_comm H τ hS

/-- Exact precomposition sends identity delta-functor morphisms to identities. -/
@[simp]
theorem map_id (G : DeltaFunctor A D) :
    map H (𝟙 G) = 𝟙 (G.precomposeExactFunctor H) := rfl

/-- Exact precomposition preserves composition of delta-functor morphisms. -/
@[simp]
theorem map_comp {G G' G'' : DeltaFunctor A D} (τ : G ⟶ G') (σ : G' ⟶ G'') :
    map H (τ ≫ σ) = map H τ ≫ map H σ := rfl

/-- Exact precomposition is a functor between categories of delta functors. -/
@[stacks 0151 "functorial exact precomposition of delta functors"]
noncomputable def functor : DeltaFunctor A D ⥤ DeltaFunctor A' D where
  obj G := G.precomposeExactFunctor H
  map τ := map H τ
  map_id := map_id H
  map_comp := map_comp H

/-- The object action of exact precomposition is the object-level constructor
`precomposeExactFunctor`. -/
@[simp]
theorem functor_obj (G : DeltaFunctor A D) :
    (functor H).obj G = G.precomposeExactFunctor H := rfl

/-- The component of a precomposed delta-functor morphism is evaluated after
the exact source functor. -/
@[simp]
theorem map_app {G G' : DeltaFunctor A D} (τ : G ⟶ G') (X : A') :
    (map H τ).app.app X = τ.app.app (H.obj.obj X) := rfl

end precomposeExactFunctor

end Precompose

end CategoryTheory.DeltaFunctor
