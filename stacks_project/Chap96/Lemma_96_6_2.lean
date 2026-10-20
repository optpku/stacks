/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.AlgebraicGeometry.GroupoidsOver.RingedTopos
import ReasLib.AlgebraicGeometry.GroupoidsOver.RingedTopos.Flat
import ReasLib.AlgebraicGeometry.Scheme.Sites.Standard.Flat
import ReasLib.AlgebraicGeometry.GroupoidsOver.RingedTopos.Representable
import ReasLib.AlgebraicGeometry.GroupoidsOver.Module.ParasiticCohomology
import StacksCheckRecall

@[expose] public section

open AlgebraicGeometry CategoryTheory FiberedCategoryOver.Groupoids
open AlgebraicGeometry.GroupoidsOver
open scoped Bicategory

universe u

variable {S : Scheme.{u}} {X Y : GroupoidsOver S} (f : X ⟶ Y) (τ : StandardTopology)

/- The canonical identification `f⁻¹ 𝒪_Y ≅ 𝒪_X` of associated `τ`-structure sheaves. -/
#check (AlgebraicGeometry.GroupoidsOver.associatedStructureSheafInverseImageIso f τ :
  ((toFunctor f).sheafPushforwardContinuous RingCat.{u}
      (X.associatedTopology τ) (Y.associatedTopology τ)).obj
    (associatedStructureSheaf Y τ) ≅ associatedStructureSheaf X τ)

variable [HasSmallAssociatedTypeSections f τ]

/- The canonical ring-valued inverse-image structure map is invertible. -/
#check (AlgebraicGeometry.GroupoidsOver.associatedRingedToposHom_structureMap_isIso f τ :
  IsIso (AlgebraicGeometry.GroupoidsOver.associatedRingedToposHom f τ).structureMap)

/- Lemma 96.6.2: let `f : 𝒳 ⟶ 𝒴` be a 1-morphism of categories fibred in
groupoids over `(Sch/S)_fppf`. Let `τ ∈ {Zariski, étale, smooth, syntomic, fppf}`.
There is a canonical identification `f⁻¹ 𝒪_𝒴 ≅ 𝒪_𝒳` which turns
`f : Sh(𝒳_τ) ⟶ Sh(𝒴_τ)` into a morphism of ringed topoi. -/
@[stacks 06TW] #check
  (AlgebraicGeometry.GroupoidsOver.associatedRingedToposHom f τ :
    RingedSite.ToposHom (associatedRingedSite X τ) (associatedRingedSite Y τ))
