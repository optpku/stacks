/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.AlgebraicGeometry.FormalDeformation.Smooth.TangentCriterion
import StacksCheckRecall

/-!
# Smoothness of a map of deformation categories from a smooth composite

If `F → G → H` are morphisms of categories cofibered in groupoids over
`ArtinianLocalAlgCat Λ k`, `F` and `G` are deformation categories, the
differential `TF → TG` is surjective, and `F → H` is smooth, then `F → G` is
smooth.
-/

open CategoryTheory
open scoped BasedFunctor Bicategory

universe u v w

/- Lemma 90.20.4: let `φ : F ⥤ᵇ G` and `ψ : G ⥤ᵇ H` be morphisms of categories
cofibered in groupoids over `ArtinianLocalAlgCat Λ k`. If `F` and `G` are deformation
categories, the map `TF → TG` given by `differential φ` is surjective, and `φ ⋙ ψ`
is smooth, then `φ` is smooth. -/
@[stacks 0E3R] #check
  (CategoryTheory.BasedFunctor.isSmooth_of_comp_surjective_differential :
    ∀ {Λ k : Type u} [CommRing Λ] [IsNoetherianRing Λ] [Field k] [Algebra Λ k]
      [Module.Finite Λ k]
      {F G H : Type v} [Category.{w} F] [Category.{w} G] [Category.{w} H]
      {p : F ⥤ ArtinianLocalAlgCat Λ k} {q : G ⥤ ArtinianLocalAlgCat Λ k}
      {r : H ⥤ ArtinianLocalAlgCat Λ k}
      [Functor.IsDeformationCategory p] [Functor.IsDeformationCategory q]
      [Functor.IsFibered.InGroupoids r.op]
      (φ : BasedCategory.ofFunctor p ⥤ᵇ BasedCategory.ofFunctor q)
      (ψ : BasedCategory.ofFunctor q ⥤ᵇ BasedCategory.ofFunctor r)
      (hsurj : Function.Surjective (BasedFunctor.differential φ))
      (hcomp : BasedFunctor.IsSmooth (φ ⋙ ψ)), BasedFunctor.IsSmooth φ)
