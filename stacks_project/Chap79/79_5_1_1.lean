/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

import StacksCheckRecall
public import stacks_project.Chap78.Definition_78_18_1_Invariant
public import stacks_project.Chap78.Lemma_78_11_2_Groupoid
public import stacks_project.Chap79.«79_5_1_1_Infinitesimal»
public import ReasLib.AlgebraicGeometry.AlgebraicSpace.Groupoid.InfinitesimalSection

@[expose] public section

open CategoryTheory AlgebraicGeometry Limits

universe u

namespace AlgebraicGeometry.GroupoidAlgebraicSpace

/- 79.5.1.1: Differential parameters and infinitesimal source sections correspond
uniquely in both directions along an invariant first-order thickening. -/
@[stacks 0CKE] #check
  (AlgebraicGeometry.GroupoidAlgebraicSpace.isPerturbation_bijective :
    ∀ {S : Scheme.{u}} [HasPullbacks (AlgebraicSpace S)] {B : AlgebraicSpace S}
      (G : GroupoidAlgebraicSpace B) {U₀ : AlgebraicSpace S} (ι : U₀ ⟶ G.U.left)
      [AlgebraicSpace.IsFirstOrderThickening ι],
      CategoryTheory.Subobject.IsInvariant G.s.left G.t.left (Subobject.mk ι) →
        (∀ θ : Parameter G ι, ∃! δ : InfinitesimalSection G ι, IsPerturbation G ι θ δ) ∧
          (∀ δ : InfinitesimalSection G ι, ∃! θ : Parameter G ι, IsPerturbation G ι θ δ))

#check
  (AlgebraicGeometry.GroupoidAlgebraicSpace.existsUnique_infinitesimalSection_of_parameter :
    ∀ {S : Scheme.{u}} [HasPullbacks (AlgebraicSpace S)] {B : AlgebraicSpace S}
      (G : GroupoidAlgebraicSpace B) {U₀ : AlgebraicSpace S} (ι : U₀ ⟶ G.U.left)
      [AlgebraicSpace.IsFirstOrderThickening ι] (θ : Parameter G ι),
      ∃! δ : InfinitesimalSection G ι, IsPerturbation G ι θ δ)

end AlgebraicGeometry.GroupoidAlgebraicSpace
