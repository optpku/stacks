/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.AlgebraicTopology.SimplicialObject.Copower.Functor.Bifunctor
public import Mathlib.Tactic.CrossRefAttribute

/-!
@stack 017E

# Projection from a simplicial copower

This module packages the canonical augmentation `copower U X ⟶ X` together with its
calculation rules and its naturality in both the simplicial-set and simplicial-object variables.
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits Opposite
open scoped Simplicial

noncomputable section

universe w v u e d

namespace CategoryTheory.SimplicialObject

variable {C : Type u} [Category.{v} C]

section Projection

variable (X : SimplicialObject C)

/-- The raw component of the canonical projection from a simplicial copower. -/
@[stacks 017E "copower projection component"]
def copower.projectionApp
    (U : SSet.{w})
    [HasCopower U X]
    (Δ : SimplexCategoryᵒᵖ) :
    (copower U X).obj Δ ⟶ X.obj Δ :=
  Limits.Sigma.desc (fun _ : U.obj Δ ↦ 𝟙 (X.obj Δ))

/-- The raw components of the copower projection form a natural family. -/
@[stacks 017E "copower projection component naturality"]
theorem copower.projectionApp.naturality
    (U : SSet.{w})
    [HasCopower U X]
    {Δ₁ Δ₂ : SimplexCategoryᵒᵖ} (σ : Δ₁ ⟶ Δ₂) :
    (copower U X).map σ ≫ copower.projectionApp X U Δ₂ =
      copower.projectionApp X U Δ₁ ≫ X.map σ := by
  change Sigma.map' (U.map σ) (fun _ ↦ X.map σ) ≫
      Sigma.desc (fun _ : U.obj Δ₂ ↦ 𝟙 (X.obj Δ₂)) =
    Sigma.desc (fun _ : U.obj Δ₁ ↦ 𝟙 (X.obj Δ₁)) ≫ X.map σ
  apply Sigma.hom_ext
  intro u
  simp only [Sigma.ι_comp_map'_assoc, Sigma.ι_desc_assoc, Sigma.ι_desc,
    Category.comp_id, Category.id_comp]

/-- The canonical projection `copower U X ⟶ X`, degreewise the coproduct map that is the
identity on every summand. -/
@[stacks 017E "simplicial copower projection"]
def copower.projection
    (U : SSet.{w})
    [HasCopower U X] :
    copower U X ⟶ X where
  app := copower.projectionApp X U
  naturality := fun {_ _} σ ↦ copower.projectionApp.naturality X U σ

/-- The component of `copower.projection` is its corresponding raw component. -/
@[simp, stacks 017E "copower projection component formula"]
theorem copower.projection_app
    (U : SSet.{w})
    [HasCopower U X]
    (Δ : SimplexCategoryᵒᵖ) :
    (copower.projection X U).app Δ = copower.projectionApp X U Δ := rfl

/-- Computing the copower projection after a coproduct injection. -/
@[simp, stacks 017E "copower projection injection formula"]
theorem copower.projection.ι
    (U : SSet.{w})
    [HasCopower U X]
    (Δ : SimplexCategoryᵒᵖ) (u : U.obj Δ) :
    Sigma.ι (fun _ : U.obj Δ ↦ X.obj Δ) u ≫ (copower.projection X U).app Δ =
      𝟙 (X.obj Δ) :=
  Sigma.ι_desc (fun _ : U.obj Δ ↦ 𝟙 (X.obj Δ)) u

end Projection

section ObjectVariable

variable (U : SSet.{w})
variable {X Y : SimplicialObject C}

/-- The copower projections are natural in the simplicial-object variable. -/
@[stacks 017E "copower projection naturality in the object variable"]
theorem copower.projection.object.naturality
    [HasCopower U X]
    [HasCopower U Y]
    (f : X ⟶ Y) :
    CommSq (copower.hom U f) (copower.projection X U)
      (copower.projection Y U) f := by
  constructor
  apply NatTrans.ext
  funext Δ
  change Limits.Sigma.map (fun _ : U.obj Δ ↦ f.app Δ) ≫
      Sigma.desc (fun _ : U.obj Δ ↦ 𝟙 (Y.obj Δ)) =
    Sigma.desc (fun _ : U.obj Δ ↦ 𝟙 (X.obj Δ)) ≫ f.app Δ
  apply Sigma.hom_ext
  intro u
  simp only [Sigma.ι_map_assoc, Sigma.ι_desc_assoc, Sigma.ι_desc,
    Category.comp_id, Category.id_comp]

variable [HasCopowers U C]

/-- The copower projections assemble into a natural transformation from `copower.functor U` to
the identity functor. -/
@[stacks 017E "copower projection natural transformation"]
def copower.projection.natTrans :
    copower.functor U ⟶ 𝟭 (SimplicialObject C) where
  app Y := copower.projection Y U
  naturality := fun {_ _} f ↦ (copower.projection.object.naturality U f).w

/-- The component of the object-variable projection is the objectwise copower projection. -/
@[simp, stacks 017E "copower projection natural-transformation component"]
theorem copower.projection.natTrans.app (Y : SimplicialObject C) :
    (copower.projection.natTrans U).app Y = copower.projection Y U := rfl

end ObjectVariable

section IndexVariable

variable {U V : SSet.{w}}
variable (X : SimplicialObject C)

/-- The copower projection is natural in the simplicial-set indexing variable. -/
@[stacks 017E "copower projection naturality in the indexing variable"]
theorem copower.projection.index.naturality
    [HasCopower U X] [HasCopower V X]
    (a : U ⟶ V) :
    CommSq (copower.indexHom X a) (copower.projection X U)
      (copower.projection X V) (𝟙 X) := by
  constructor
  apply NatTrans.ext
  funext Δ
  change Sigma.map' (a.app Δ) (fun _ ↦ 𝟙 (X.obj Δ)) ≫
      Sigma.desc (fun _ : V.obj Δ ↦ 𝟙 (X.obj Δ)) =
    Sigma.desc (fun _ : U.obj Δ ↦ 𝟙 (X.obj Δ)) ≫ 𝟙 (X.obj Δ)
  apply Sigma.hom_ext
  intro u
  simp only [Sigma.ι_comp_map'_assoc, Sigma.ι_desc, Category.comp_id]

variable [X.HasCopowersOf]

namespace copower.indexFunctor

/-- The copower projections assemble into a natural transformation from the simplicial-set
variable copower functor to the constant functor at `X`. -/
@[stacks 017E "projection from the index-variable copower functor"]
def projection :
    copower.indexFunctor X ⟶ (Functor.const SSet.{w}).obj X where
  app U := copower.projection X U
  naturality := fun {_ _} a ↦ (copower.projection.index.naturality X a).w

/-- The component of the index-variable projection is the objectwise copower projection. -/
@[simp, stacks 017E "index-variable copower projection component"]
theorem projection.app (U : SSet.{w}) :
    (projection X).app U = copower.projection X U := rfl

end copower.indexFunctor

end IndexVariable

section BifunctorProjection

variable {D : Type d} [Category.{e} D]
variable (K : D ⥤ SSet.{w})
variable [HasCopowers.OfIndex K C]

/-- Naturality in the indexing variable of the projection from the curried copower bifunctor. -/
@[stacks 017E "indexed copower projection naturality"]
theorem copower.ofIndex.projection.naturality {d d' : D} (f : d ⟶ d') :
    copower.indexHom.natTrans (K.map f) ≫ copower.projection.natTrans (K.obj d') =
      copower.projection.natTrans (K.obj d) ≫
        ((Functor.const D).obj (𝟭 (SimplicialObject C))).map f := by
  apply NatTrans.ext
  funext X
  change copower.indexHom X (K.map f) ≫ copower.projection X (K.obj d') =
    copower.projection X (K.obj d) ≫ 𝟙 X
  exact (copower.projection.index.naturality X (K.map f)).w

/-- The canonical map from a copower to its simplicial-object variable is natural in both
variables. -/
@[stacks 017E "bifunctorial copower projection"]
def copower.ofIndex.projection :
    copower.ofIndex K ⟶ (Functor.const D).obj (𝟭 (SimplicialObject C)) where
  app d := copower.projection.natTrans (K.obj d)
  naturality := fun {_ _} f ↦ copower.ofIndex.projection.naturality K f

/-- The component of the bifunctorial copower projection is the canonical copower projection. -/
@[simp, stacks 017E "indexed copower projection component"]
theorem copower.ofIndex.projection.app (d : D)
    (X : SimplicialObject C) :
    ((copower.ofIndex.projection K).app d).app X =
      copower.projection X (K.obj d) := rfl

end BifunctorProjection

end CategoryTheory.SimplicialObject
