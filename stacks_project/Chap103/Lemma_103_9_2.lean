/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.AlgebraicGeometry.GroupoidsOver.Module.Parasitic
import StacksCheckRecall

/-! # Stability and descent of parasitic modules -/

@[expose] public section

open AlgebraicGeometry CategoryTheory CategoryTheory.ObjectProperty
open AlgebraicGeometry.GroupoidsOver
open scoped Bicategory

universe u v

/- Lemma 103.9.2 (1): flat inverse image preserves parasitic module presheaves. -/
@[stacks 0774] #check (AlgebraicGeometry.GroupoidsOver.IsParasitic.inverseImage :
  ∀ {S : Scheme.{u}} {X Y : GroupoidsOver S} [AlgebraicStack X] [AlgebraicStack Y]
    (g : Y ⟶ X) [AlgebraicStack.Flat g]
    (F : PresheafOfModules.{u} (structureSheaf X).obj) [IsParasitic F],
    IsParasitic ((presheafModuleInverseImage g).obj F))

/- Lemma 103.9.2 (2): standard-topology sheafification preserves parasiticity. -/
@[stacks 0774] #check (AlgebraicGeometry.GroupoidsOver.IsParasitic.sheafification :
  ∀ {S : Scheme.{u}} {X : GroupoidsOver S} [AlgebraicStack X]
    (τ : StandardTopology) (F : PresheafOfModules.{u} (structureSheaf X).obj)
    [IsParasitic F],
    IsParasitic (associatedModulePresheaf
      ((PresheafOfModules.sheafification.{u}
        (associatedStructurePresheafIso X τ).hom).obj F)))

/- Lemma 103.9.2 (3): parasitic module sheaves form a Serre subcategory. -/
@[stacks 0774] #check (AlgebraicGeometry.GroupoidsOver.associatedModules.parasiticIsSerreClass :
  ∀ {S : Scheme.{u}} (X : GroupoidsOver S) [AlgebraicStack X] (τ : StandardTopology),
    IsSerreClass (associatedModules.parasitic X τ))

/- Lemma 103.9.2 (4): parasiticity of étale modules descends along smooth covers. -/
@[stacks 0774] #check (AlgebraicGeometry.GroupoidsOver.IsParasitic.ofSmoothCover :
  ∀ {S : Scheme.{u}} {X : GroupoidsOver S} [AlgebraicStack X]
    {ι : Type v} {Xi : ι → GroupoidsOver S} [∀ i, AlgebraicStack (Xi i)]
    (f : ∀ i, Xi i ⟶ X) [∀ i, AlgebraicStack.Smooth (f i)],
    (∀ y : AlgebraicStack.Points X,
      ∃ i, y ∈ Set.range (AlgebraicStack.Points.map (f i))) →
    ∀ (F : etaleModules X),
      (∀ i, IsParasitic (etaleModulePresheaf ((etaleModuleInverseImage (f i)).obj F))) →
      IsParasitic (etaleModulePresheaf F))

/- Lemma 103.9.2 (5): parasiticity of fppf modules descends along fppf covers. -/
@[stacks 0774] #check (AlgebraicGeometry.GroupoidsOver.IsParasitic.ofFppfCover :
  ∀ {S : Scheme.{u}} {X : GroupoidsOver S} [AlgebraicStack X]
    {ι : Type v} {Xi : ι → GroupoidsOver S} [∀ i, AlgebraicStack (Xi i)]
    (f : ∀ i, Xi i ⟶ X) [∀ i, AlgebraicStack.Flat (f i)]
    [∀ i, AlgebraicStack.LocallyOfFinitePresentation (f i)],
    (∀ y : AlgebraicStack.Points X,
      ∃ i, y ∈ Set.range (AlgebraicStack.Points.map (f i))) →
    ∀ (F : SheafOfModules.{u} (structureSheaf X)),
      (∀ i, IsParasitic ((presheafModuleInverseImage (f i)).obj F.val)) →
      IsParasitic F.val)
