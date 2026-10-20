/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.AlgebraicGeometry.Scheme.Module.Derived.PseudoCoherent.Affine
public import stacks_project.Chap36.Lemma_36_10_1_PseudoCoherent
import StacksCheckRecall

@[expose] public section

open CategoryTheory ComplexShape

noncomputable section

universe u

/- Lemma 36.10.2 (1): for an affine scheme `Spec R`, the derived object associated to a
cochain complex `M` by degreewise affine tilde sheafification is `m`-pseudo-coherent if and only
if `M` is `m`-pseudo-coherent over `R`. -/
@[stacks 08E7] #check
  (AlgebraicGeometry.tilde.isMPseudoCoherent_iff :
    ∀ (R : CommRingCat.{u}) (M : CochainComplex (ModuleCat R) ℤ) (m : ℤ),
      AlgebraicGeometry.Scheme.IsMPseudoCoherent (AlgebraicGeometry.Spec (.of R))
          (DerivedCategory.Q.obj
            (((AlgebraicGeometry.tilde.functor R).mapHomologicalComplex (up ℤ)).obj M)) m ↔
        CategoryTheory.CochainComplex.IsMPseudoCoherent M m)

/- Lemma 36.10.2 (2): for an affine scheme `Spec R`, the derived object associated to a
cochain complex `M` by degreewise affine tilde sheafification is pseudo-coherent if and only if
`M` is pseudo-coherent over `R`. -/
@[stacks 08E7] #check
  (AlgebraicGeometry.tilde.isPseudoCoherent_iff :
    ∀ (R : CommRingCat.{u}) (M : CochainComplex (ModuleCat R) ℤ),
      AlgebraicGeometry.Scheme.IsPseudoCoherent (AlgebraicGeometry.Spec (.of R))
          (DerivedCategory.Q.obj
            (((AlgebraicGeometry.tilde.functor R).mapHomologicalComplex (up ℤ)).obj M)) ↔
        CategoryTheory.CochainComplex.IsPseudoCoherent M)
