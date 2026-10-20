/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.CategoryTheory.Sites.QuasiCompact
import StacksCheckRecall

@[expose] public section

open CategoryTheory

universe u v

variable {C : Type u} [Category.{v} C] (K : Precoverage C) (U : C)

/- Definition 7.17.1: let C be a site. An object U of C is quasi-compact if
given a covering 𝒰 = {Uᵢ ⟶ U}_{i ∈ I} in C there exists another covering
𝒱 = {Vⱼ ⟶ U}_{j ∈ J} and a morphism 𝒱 ⟶ 𝒰 of families of maps with fixed
target given by id : U ⟶ U, α : J → I, and Vⱼ ⟶ U_{α(j)} (see Definition
7.8.1) such that the image of α is a finite subset of I. This is owned by
Precoverage.QuasiCompactObject. -/
@[stacks 090H] #check (CategoryTheory.Precoverage.QuasiCompactObject K U : Prop)

#check (CategoryTheory.Precoverage.quasiCompactObject_iff_finite_image_refinement K U :
  K.QuasiCompactObject U ↔
    ∀ (𝒰 : SemiRepresentableFamily.Over.{max u v} U), 𝒰.toPresieve ∈ K U →
      ∃ (𝒱 : SemiRepresentableFamily.Over.{max u v} U), 𝒱.toPresieve ∈ K U ∧
        ∃ (φ : SemiRepresentableFamily.Over.Hom 𝒱 𝒰),
          Set.Finite (Set.range φ.α))
