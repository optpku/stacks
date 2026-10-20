/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.AlgebraicGeometry.AlgebraicSpace.GlobalSections.Affine
import StacksCheckRecall

@[expose] public section

open CategoryTheory AlgebraicGeometry

universe u

/- Lemma 66.33.1: Let X be an algebraic space over Spec ℤ. Let T be an affine scheme.
The map Mor(X, T) ⟶ Hom(Γ(T, ⊤), Γ(X, 𝒪_X)) which maps f to f^♯ on global sections
is bijective. -/
@[stacks 05Z1] #check (AlgebraicGeometry.AlgebraicSpace.GlobalSections.homEquivAffine :
  ∀ {X : AlgebraicGeometry.AlgebraicSpace AlgebraicGeometry.AlgebraicSpace.specZ.{u}}
    {T : AlgebraicGeometry.Scheme.{u}} [AlgebraicGeometry.IsAffine T],
    (X ⟶ AlgebraicGeometry.AlgebraicSpace.ofOver (AlgebraicGeometry.AlgebraicSpace.overSpecZ T)) ≃
      (Γ(T, ⊤) ⟶ AlgebraicGeometry.AlgebraicSpace.globalSectionsRing X))
#check AlgebraicGeometry.AlgebraicSpace.GlobalSections.homEquivAffine_apply
#check AlgebraicGeometry.AlgebraicSpace.GlobalSections.homEquivAffine_symm_apply
