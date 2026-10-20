/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.Algebra.Category.ModuleCat.Sheaf.Internal
public import ReasLib.AlgebraicGeometry.GroupoidsOver.RingedTopos
public import ReasLib.AlgebraicGeometry.GroupoidsOver.Modules
public import ReasLib.AlgebraicGeometry.RingedSite.Topos.HomOfCocontinuous
public import ReasLib.CategoryTheory.Fibered.InheritedTopology.Morphism
public import stacks_project.Chap96.Lemma_96_8_1_RingedSite

@[expose] public section
open AlgebraicGeometry CategoryTheory FiberedCategoryOver.Groupoids
open scoped Bicategory
universe u
variable {S : Scheme.{u}} {X Y : GroupoidsOver S} (f : X ⟶ Y) (τ : StandardTopology)

#check (AlgebraicGeometry.GroupoidsOver.associatedStructureSheafInverseImageIso f τ :
  ((toFunctor f).sheafPushforwardContinuous RingCat.{u}
    (X.associatedTopology τ) (Y.associatedTopology τ)).obj
    (AlgebraicGeometry.GroupoidsOver.associatedStructureSheaf Y τ) ≅
    AlgebraicGeometry.GroupoidsOver.associatedStructureSheaf X τ)

variable [AlgebraicGeometry.GroupoidsOver.HasSmallAssociatedTypeSections f τ]
#check (AlgebraicGeometry.GroupoidsOver.associatedRingedToposHom f τ :
  RingedSite.ToposHom (AlgebraicGeometry.GroupoidsOver.associatedRingedSite X τ)
    (AlgebraicGeometry.GroupoidsOver.associatedRingedSite Y τ))
