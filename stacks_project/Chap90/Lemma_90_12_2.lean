/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.AlgebraicGeometry.FormalDeformation.TangentSpace.Tensor
import StacksCheckRecall

/-!
# Lemma 90.12.2

If `F` is a predeformation category whose associated isomorphism-class functor
`F-bar` satisfies (S2), then `T F` carries a natural `k`-vector space structure,
and `F-bar(k[V])` identifies with `T F ⊗[k] V` functorially in every finite-dimensional
`k`-vector space `V`.
-/

@[expose] public section

noncomputable section

open CategoryTheory
open CategoryTheory.Functor
open ArtinianLocalAlgCat
open scoped TensorProduct

universe u v w

variable {Λ k : Type u} [CommRing Λ] [IsNoetherianRing Λ] [Field k] [Algebra Λ k]
  [Module.Finite Λ k]
variable {F : Type v} [Category.{w} F]
variable (p : F ⥤ ArtinianLocalAlgCat Λ k)
variable [IsPredeformationCategory p] [HasSchlessingerH2 (fiberIsoClassFunctor p)]

/- Let `F` be a predeformation category such that
`F-bar` satisfies (S2). Then `T F` has a natural `k`-vector space structure. -/
#check (CategoryTheory.Functor.instModule_fiberDualTangent p :
    Module k ((fiberIsoClassFunctor p).obj (dualNumber Λ k)))

/- Lemma 90.12.2: The tangent space has a natural vector-space structure, and its
canonical tensor comparison is bijective for every finite-dimensional vector space. -/
@[stacks 06IH] #check (CategoryTheory.Functor.bijective_fiberDualTangentTensor :
  ∀ (p : F ⥤ ArtinianLocalAlgCat Λ k) [IsPredeformationCategory p]
    [HasSchlessingerH2 (fiberIsoClassFunctor p)] (V : FGModuleCat.{u} k),
    Function.Bijective (CategoryTheory.Functor.fiberDualTangentTensor p V))
