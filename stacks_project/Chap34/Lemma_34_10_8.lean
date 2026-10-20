/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.AlgebraicGeometry.Scheme.Cover.V.Stability
import StacksCheckRecall

@[expose] public section

open CategoryTheory
open CategoryTheory.Limits

universe u v

/-!
# Lemma 34.10.8

This chapter entry is a compatibility facade for refinement and coproduct
characterizations of `V` covers.
-/

/- Lemma 34.10.8 (1): a family is a `V` cover exactly when it admits a
refining `V` cover. -/
@[stacks 0ETI] #check
  (AlgebraicGeometry.isVCovering_iff_exists_refinement :
    ∀ {ι : Type v} {T : AlgebraicGeometry.Scheme.{u}}
        (family : ι → AlgebraicGeometry.Scheme.{u})
        (map : ∀ i, family i ⟶ T),
      AlgebraicGeometry.IsVCovering T family map ↔
        ∃ (κ : Type v) (refining : κ → AlgebraicGeometry.Scheme.{u})
            (refiningMap : ∀ k, refining k ⟶ T),
          AlgebraicGeometry.IsVCovering T refining refiningMap ∧
            CategoryTheory.SemiRepresentableFamily.Over.Refines
              (CategoryTheory.SemiRepresentableFamily.Over.ofArrows refining refiningMap)
              (CategoryTheory.SemiRepresentableFamily.Over.ofArrows family map))

/- Lemma 34.10.8 (2): a family is a `V` cover exactly when its coproduct map,
viewed as a singleton family, is a `V` cover. -/
@[stacks 0ETI] #check
  (AlgebraicGeometry.isVCovering_iff_sigmaDesc :
    ∀ {ι : Type v} {T : AlgebraicGeometry.Scheme.{u}} [Small.{u} ι]
        (family : ι → AlgebraicGeometry.Scheme.{u})
        (map : ∀ i, family i ⟶ T),
      AlgebraicGeometry.IsVCovering T family map ↔
        AlgebraicGeometry.IsVCovering T (fun _ : PUnit ↦ ∐ family)
          (fun _ ↦ CategoryTheory.Limits.Sigma.desc map))
