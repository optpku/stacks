/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.AlgebraicGeometry.GroupoidsOver.Etale.FlatBaseChange
import StacksCheckRecall

@[expose] public section

open AlgebraicGeometry CategoryTheory

universe u

/- Definition 103.7.1: let `X` be an algebraic stack and let `F` in
`Mod(X_étale, 𝒪_X)`. We say `F` has the flat base change property if and only
if the comparison `c_φ : f_small^*(F|_{U'_étale}) ⟶ F|_{U_étale}` is an
isomorphism whenever `φ : x ⟶ x'` lies over a flat morphism of schemes
`f : U ⟶ U'`. -/
@[stacks 0762] #check (AlgebraicGeometry.GroupoidsOver.HasFlatBaseChange :
  ∀ {S : Scheme.{u}} {X : AlgebraicGeometry.GroupoidsOver S}
    [AlgebraicGeometry.AlgebraicStack X],
    AlgebraicGeometry.GroupoidsOver.etaleModules X → Prop)
