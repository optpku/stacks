/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

import StacksCheckRecall
public import ReasLib.AlgebraicGeometry.AlgebraicStack.Lift.EtaleLocalIso

/-!
# Étale-local isomorphism of smooth cartesian lifts along a thickening
-/

@[expose] public section

open CategoryTheory AlgebraicGeometry AlgebraicGeometry.AlgebraicStack Limits Bicategory
open scoped Bicategory

universe u

/- Lemma 106.6.6. Smooth cartesian lifts across a thickening of algebraic stacks
admit an étale-local comparison agreeing with the initial diagram over the common
closed algebraic space. -/
@[stacks 0CJW] #check
  (AlgebraicGeometry.AlgebraicStack.Lift.exists_etaleCovering_iso :
    ∀ {S : Scheme.{u}} {X X' : GroupoidsOver S}
    [AlgebraicStack X] [AlgebraicStack X'] (iX : X ⟶ X') [IsThickening iX]
    {W W' W'' : AlgebraicSpace S} (x : W.toGroupoids ⟶ X)
    (x' : W'.toGroupoids ⟶ X') (x'' : W''.toGroupoids ⟶ X')
    [Groupoids.Hom.Smooth x] [Groupoids.Hom.Smooth x'] [Groupoids.Hom.Smooth x'']
    (i : W ⟶ W') (i'' : W ⟶ W'')
    (α' : x ≫ iX ≅ AlgebraicSpace.toGroupoids.map i ≫ x')
    (α'' : x ≫ iX ≅ AlgebraicSpace.toGroupoids.map i'' ≫ x'')
    (h' : PseudoPullbackCone.IsBilimit
      (⟨W.toGroupoids, x, AlgebraicSpace.toGroupoids.map i, α'⟩ :
        PseudoPullbackCone iX x'))
    (h'' : PseudoPullbackCone.IsBilimit
      (⟨W.toGroupoids, x, AlgebraicSpace.toGroupoids.map i'', α''⟩ :
        PseudoPullbackCone iX x'')),
    ∃ (ι : Type u) (Wk : ι → AlgebraicSpace S) (f' : ∀ k, Wk k ⟶ W')
      (f'' : ∀ k, Wk k ⟶ W'')
      (γ : ∀ k, AlgebraicSpace.toGroupoids.map (f'' k) ≫ x'' ≅
        AlgebraicSpace.toGroupoids.map (f' k) ≫ x'),
      AlgebraicGeometry.AlgebraicStack.Lift.IsEtaleLocalIso α' α'' f' f'' γ)
