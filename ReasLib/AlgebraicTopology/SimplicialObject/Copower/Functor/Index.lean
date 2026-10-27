/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.AlgebraicTopology.SimplicialObject.Copower.Functor.Object
public import Mathlib.Tactic.CrossRefAttribute

/-!
# Functoriality of simplicial copowers in the indexing variable

A morphism of indexing simplicial sets reindexes a copower. This file owns the pointwise
reindexing maps, their interaction with the object variable, the index functor, and the natural
transformation between fixed-index copower functors.
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits Opposite
open scoped Simplicial

noncomputable section

universe w v u

namespace CategoryTheory.SimplicialObject

variable {C : Type u} [Category.{v} C]

section IndexVariable

variable {U V : SSet.{w}}
variable (X : SimplicialObject C)

/-- The raw component induced on copowers by a morphism of indexing simplicial sets. -/
@[stacks 017E "copower index-map component"]
abbrev copower.indexHomApp
    [HasCopower U X] [HasCopower V X]
    (a : U ⟶ V) (Δ : SimplexCategoryᵒᵖ) :
    (copower U X).obj Δ ⟶ (copower V X).obj Δ :=
  Functor.indexedCoprod.indexHomApp X a Δ

/-- The raw components induced by reindexing form a natural family. -/
@[stacks 017E "copower index-map naturality"]
theorem copower.indexHomApp.naturality
    [HasCopower U X] [HasCopower V X]
    (a : U ⟶ V) {Δ₁ Δ₂ : SimplexCategoryᵒᵖ} (σ : Δ₁ ⟶ Δ₂) :
    (copower U X).map σ ≫ copower.indexHomApp X a Δ₂ =
      copower.indexHomApp X a Δ₁ ≫ (copower V X).map σ := by
  dsimp only [copower, copower.indexHomApp, Functor.indexedCoprod,
    Functor.indexedCoprod.mapHom, Functor.indexedCoprod.indexHomApp]
  apply Sigma.hom_ext
  intro u
  simpa only [Sigma.ι_comp_map'_assoc, Sigma.ι_comp_map', Category.id_comp,
    Category.comp_id] using
    congrArg (fun t ↦ X.map σ ≫ Sigma.ι (fun _ : V.obj Δ₂ ↦ X.obj Δ₂) t)
      (a.naturality_apply σ u)

/-- The morphism of simplicial copowers induced by a morphism `a : U ⟶ V` of simplicial sets
in the indexing variable. Degreewise, it reindexes the coproduct by `a.app Δ`. -/
@[stacks 017E "copower morphism in the indexing variable"]
abbrev copower.indexHom
    [HasCopower U X] [HasCopower V X]
    (a : U ⟶ V) :
    copower U X ⟶ copower V X :=
  Functor.indexedCoprod.indexHom X a

/-- The component of `copower.indexHom` is its corresponding raw component. -/
@[simp, stacks 017E "copower index-map component formula"]
theorem copower.indexHom_app
    [HasCopower U X] [HasCopower V X]
    (a : U ⟶ V) (Δ : SimplexCategoryᵒᵖ) :
    (copower.indexHom X a).app Δ = copower.indexHomApp X a Δ := rfl

/-- Computing `copower.indexHom` after a coproduct injection. -/
@[simp, stacks 017E "copower index-map injection formula"]
theorem copower.indexHom.ι
    [HasCopower U X] [HasCopower V X]
    (a : U ⟶ V) (Δ : SimplexCategoryᵒᵖ) (u : U.obj Δ) :
    Sigma.ι (fun _ : U.obj Δ ↦ X.obj Δ) u ≫ (copower.indexHom X a).app Δ =
      Sigma.ι (fun _ : V.obj Δ ↦ X.obj Δ) (a.app Δ u) := by
  dsimp only [copower, Functor.indexedCoprod, copower.indexHom,
    Functor.indexedCoprod.indexHom,
    Functor.indexedCoprod.indexHomApp]
  rw [Sigma.ι_comp_map', Category.id_comp]

/-- Identity law for `copower.indexHom`. -/
@[simp, stacks 017E "copower index-map identity"]
theorem copower.indexHom.id
    (U : SSet.{w})
    [HasCopower U X] :
    copower.indexHom X (𝟙 U) = 𝟙 (copower U X) := by
  apply NatTrans.ext
  funext Δ
  dsimp only [copower, Functor.indexedCoprod, copower.indexHom,
    Functor.indexedCoprod.indexHom, Functor.indexedCoprod.indexHomApp]
  exact Sigma.map'_id_id

/-- Composition law for `copower.indexHom`. -/
@[stacks 017E "copower index-map composition"]
theorem copower.indexHom.comp
    {U₁ U₂ U₃ : SSet.{w}}
    [HasCopower U₁ X] [HasCopower U₂ X] [HasCopower U₃ X]
    (a : U₁ ⟶ U₂) (b : U₂ ⟶ U₃) :
    copower.indexHom X (a ≫ b) = copower.indexHom X a ≫ copower.indexHom X b := by
  apply NatTrans.ext
  funext Δ
  dsimp only [copower, Functor.indexedCoprod, copower.indexHom,
    Functor.indexedCoprod.indexHom, Functor.indexedCoprod.indexHomApp]
  apply Sigma.hom_ext
  intro u
  simp only [NatTrans.comp_app, Functor.indexedCoprod.indexHomApp,
    Sigma.ι_comp_map'_assoc, Sigma.ι_comp_map', Category.id_comp, types_comp_apply]

variable [X.HasCopowersOf]

/-- The functor `U ↦ copower U X` in the simplicial-set variable. -/
@[stacks 017E "copower functor in the indexing variable"]
abbrev copower.indexFunctor : SSet.{w} ⥤ SimplicialObject C :=
  Functor.indexedCoprod.indexFunctor X

end IndexVariable

section MixedVariable

variable {U V : SSet.{w}} (X : SimplicialObject C)

/-- Reindexing a copower is natural in the simplicial-object variable. This interchange law is
the compatibility needed to package copower as a bifunctor. -/
@[stacks 017E "copower variable interchange"]
theorem copower.indexHom.naturality
    {Y : SimplicialObject C}
    [HasCopower U X] [HasCopower U Y] [HasCopower V X] [HasCopower V Y]
    (a : U ⟶ V) (f : X ⟶ Y) :
    CommSq (copower.hom U f) (copower.indexHom X a)
      (copower.indexHom Y a) (copower.hom V f) := by
  constructor
  apply NatTrans.ext
  funext Δ
  dsimp only [copower, Functor.indexedCoprod, copower.hom, copower.indexHom,
    Functor.indexedCoprod.hom,
    Functor.indexedCoprod.homApp, Functor.indexedCoprod.indexHom,
    Functor.indexedCoprod.indexHomApp]
  apply Sigma.hom_ext
  intro u
  simp only [NatTrans.comp_app, Functor.indexedCoprod.homApp,
    Functor.indexedCoprod.indexHomApp, Sigma.ι_map_assoc, Sigma.ι_comp_map'_assoc, Sigma.ι_map,
    Sigma.ι_comp_map', Category.id_comp]

end MixedVariable

section IndexNaturalTransformation

variable {U V : SSet.{w}}
variable [HasCopowers U C] [HasCopowers V C]

/-- A map of indexing simplicial sets induces a natural transformation between the corresponding
copower functors. -/
@[stacks 017E "copower functoriality in the indexing variable"]
abbrev copower.indexHom.natTrans (a : U ⟶ V) :
    copower.functor (C := C) U ⟶ copower.functor (C := C) V :=
  Functor.indexedCoprod.indexHom.natTrans (C := C) a

/-- The component of the natural transformation induced by a map of indexing simplicial sets. -/
@[simp, stacks 017E "copower index natural-transformation component"]
theorem copower.indexHom.natTrans.app (a : U ⟶ V) (X : SimplicialObject C) :
    (copower.indexHom.natTrans (C := C) a).app X = copower.indexHom X a := rfl

/-- The copower index natural transformation associated to an identity is the identity. -/
@[simp, stacks 017E "copower index natural-transformation identity"]
theorem copower.indexHom.natTrans.id (U : SSet.{w}) [HasCopowers U C] :
    copower.indexHom.natTrans (C := C) (𝟙 U) =
      𝟙 (copower.functor (C := C) U) := by
  apply NatTrans.ext
  funext X
  exact copower.indexHom.id X U

/-- Copower index natural transformations preserve composition. -/
@[stacks 017E "copower index natural-transformation composition"]
theorem copower.indexHom.natTrans.comp {U V W : SSet.{w}}
    [HasCopowers U C] [HasCopowers V C] [HasCopowers W C]
    (a : U ⟶ V) (b : V ⟶ W) :
    copower.indexHom.natTrans (C := C) (a ≫ b) =
      copower.indexHom.natTrans (C := C) a ≫
        copower.indexHom.natTrans (C := C) b := by
  apply NatTrans.ext
  funext X
  exact copower.indexHom.comp X a b

end IndexNaturalTransformation

end CategoryTheory.SimplicialObject
