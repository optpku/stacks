/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.Algebra.Homology.DerivedCategory.PseudoCoherent.ProductCriterion
import StacksCheckRecall

/-!
# Pseudo-coherence through product comparisons

This file is the source-facing recall for Lemma 15.66.5.

@stack 0CYB
-/

@[expose] public section

open CategoryTheory

universe u

/- Lemma 15.66.5 (1): for `K ∈ D⁻(R)`, pseudo-coherence is equivalent to derived tensoring by
`K` commuting with products of arbitrary, constant, or regular module families. -/
@[stacks 0CYB "Lemma 15.66.5 (1)"]
#check fun {R : Type u} [CommRing R] (K : D⁻((ModuleCat.{u} R))) ↦
  (DerivedCategory.IsPseudoCoherent.ProductCriterion.pseudoCoherent_tfae K :
    List.TFAE [
      K.obj.IsPseudoCoherent,
      ∀ {A : Type u} (Q : A → ModuleCat.{u} R),
        IsIso (DerivedCategory.IsPseudoCoherent.ProductCriterion.comparison K.obj Q),
      ∀ (Q : ModuleCat.{u} R) (A : Type u),
        IsIso (DerivedCategory.IsPseudoCoherent.ProductCriterion.comparison
          K.obj (fun _ : A ↦ Q)),
      ∀ A : Type u,
        IsIso (DerivedCategory.IsPseudoCoherent.ProductCriterion.comparison
          K.obj (fun _ : A ↦ ModuleCat.of R R))
    ])

/- Lemma 15.66.5 (2): `m`-pseudo-coherence is detected by the same comparisons on homology above
degree `m`, together with epimorphy in degree `m`. -/
@[stacks 0CYB "Lemma 15.66.5 (2)"]
#check fun {R : Type u} [CommRing R] (K : D⁻((ModuleCat.{u} R))) (m : ℤ) ↦
  (DerivedCategory.IsPseudoCoherent.ProductCriterion.mPseudoCoherent_tfae K m :
    List.TFAE [
      K.obj.IsMPseudoCoherent m,
      ∀ {A : Type u} (Q : A → ModuleCat.{u} R),
        DerivedCategory.IsPseudoCoherent.ProductCriterion.IsIsoAboveAndEpiAt m
          (DerivedCategory.IsPseudoCoherent.ProductCriterion.comparison K.obj Q),
      ∀ (Q : ModuleCat.{u} R) (A : Type u),
        DerivedCategory.IsPseudoCoherent.ProductCriterion.IsIsoAboveAndEpiAt m
          (DerivedCategory.IsPseudoCoherent.ProductCriterion.comparison
            K.obj (fun _ : A ↦ Q)),
      ∀ A : Type u,
        DerivedCategory.IsPseudoCoherent.ProductCriterion.IsIsoAboveAndEpiAt m
          (DerivedCategory.IsPseudoCoherent.ProductCriterion.comparison
            K.obj (fun _ : A ↦ ModuleCat.of R R))
    ])

/- The comparison morphism and its cutoff predicate are canonical setup owners. -/
#check @DerivedCategory.IsPseudoCoherent.ProductCriterion.comparison

#check @DerivedCategory.IsPseudoCoherent.ProductCriterion.IsIsoAboveAndEpiAt
