/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.AlgebraicGeometry.FormalDeformation.InfinitesimalAutomorphisms.ResidueChange
import StacksCheckRecall

/-!
# Lemma 90.29.4

In Situation 90.29.1, if `p` is a deformation category, there is a canonical
bijective `l`-linear comparison `Inf(p) ⊗[k] l ⟶ Inf(p_{l/k})` of infinitesimal
automorphism spaces.
-/

@[expose] public section

noncomputable section

open CategoryTheory hiding Linear
open CategoryTheory.Functor
open ArtinianLocalAlgCat
open scoped TensorProduct

universe u v w

variable (Λ k l : Type u) [CommRing Λ] [IsNoetherianRing Λ]
  [Field k] [Algebra Λ k] [Module.Finite Λ k]
  [Field l] [Algebra Λ l] [Module.Finite Λ l]
  [Algebra k l] [IsScalarTower Λ k l] [Module.Finite k l]
variable {F : Type v} [Category.{w} F] (p : F ⥤ ArtinianLocalAlgCat Λ k)
variable [IsDeformationCategory p]

/- Lemma 90.29.4 -/
@[stacks 07WC] #check
  (ArtinianLocalAlgCat.residueChangeOver.bijective_infAutTensor Λ k l p :
    Function.Bijective (ArtinianLocalAlgCat.residueChangeOver.infAutTensor Λ k l p))
