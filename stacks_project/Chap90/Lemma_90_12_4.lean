/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.AlgebraicGeometry.FormalDeformation.Differential
public import stacks_project.Chap90.Lemma_90_12_2_Tensor
import StacksCheckRecall

/-!
# Lemma 90.12.4

A morphism of predeformation categories induces a `k`-linear map on tangent
spaces whenever the associated isomorphism-class functors both satisfy (S2).
-/

@[expose] public section

noncomputable section

open CategoryTheory ArtinianLocalAlgCat Functor
open scoped Bicategory

universe u v w

variable {Λ k : Type u} [CommRing Λ] [IsNoetherianRing Λ] [Field k] [Algebra Λ k]
  [Module.Finite Λ k]
variable {F G : Type v} [Category.{w} F] [Category.{w} G]
variable {p : F ⥤ ArtinianLocalAlgCat Λ k} {q : G ⥤ ArtinianLocalAlgCat Λ k}
variable [IsPredeformationCategory p] [IsPredeformationCategory q]
variable [HasSchlessingerH2 (fiberIsoClassFunctor p)]
  [HasSchlessingerH2 (fiberIsoClassFunctor q)]

/- Lemma 90.12.4: a morphism of predeformation categories has a linear differential
when both associated isomorphism-class functors satisfy (S2). -/
@[stacks 06IJ]
#check (CategoryTheory.BasedFunctor.isLinearMap_differential :
  ∀ (φ : BasedCategory.ofFunctor p ⥤ᵇ BasedCategory.ofFunctor q),
    (IsLinearMap k :
      ((fiberIsoClassFunctor p).obj (dualNumber Λ k) →
        (fiberIsoClassFunctor q).obj (dualNumber Λ k)) → Prop)
      (CategoryTheory.BasedFunctor.differential φ))
