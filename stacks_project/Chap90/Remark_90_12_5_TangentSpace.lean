/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.AlgebraicGeometry.FormalDeformation.TangentSpace.At
public import stacks_project.Chap90.Lemma_90_12_4
import StacksCheckRecall

/-!
# Tangent space at a residue-fibre object

The tangent space `T_x F` of a category cofibered in groupoids is the tangent
space of the residue slice `F_x`. The differential `d_x φ` is the differential
of the induced slice morphism `φ_x`.
-/

@[expose] public section

noncomputable section

open CategoryTheory ArtinianLocalAlgCat Functor
open scoped Bicategory

universe u v w

/- Remark 90.12.5: the differential at a residue-fibre object is the map on tangent
spaces induced by the corresponding morphism of residue slices. -/
@[stacks 06IK] #check
  (CategoryTheory.BasedFunctor.differentialAt :
    ∀ {Λ k : Type u} [CommRing Λ] [IsNoetherianRing Λ] [Field k] [Algebra Λ k]
      [Module.Finite Λ k] {F G : Type v} [Category.{w} F] [Category.{w} G]
      {p : F ⥤ ArtinianLocalAlgCat Λ k} {q : G ⥤ ArtinianLocalAlgCat Λ k}
      [IsFibered.InGroupoids p.op] [IsFibered.InGroupoids q.op]
      (φ : BasedCategory.ofFunctor p ⥤ᵇ BasedCategory.ofFunctor q)
      (x : p.Fiber (residue Λ k)),
      CategoryTheory.Functor.tangentSpaceAt p x →
        CategoryTheory.Functor.tangentSpaceAt q (CategoryTheory.BasedFunctor.objAt φ x))
