/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

import StacksCheckRecall
import ReasLib.AlgebraicGeometry.AlgebraicSpace.Groupoid.InfinitesimalSection.Composition

/-!
# Composition of infinitesimal source sections is addition of parameters

The canonical perturbation bijection carries parameter addition to section composition.
-/

open CategoryTheory AlgebraicGeometry Limits
open AlgebraicGeometry.GroupoidAlgebraicSpace
open CategoryTheory.Preadditive

universe u

/- Lemma 79.5.2: The bijection 79.5.1.1 is an isomorphism of groups. -/
@[stacks 0CKF] #check
  (AlgebraicGeometry.GroupoidAlgebraicSpace.isPerturbation_comp :
    ∀ {S : Scheme.{u}} [HasPullbacks (AlgebraicSpace S)]
      {B : AlgebraicSpace S} (G : GroupoidAlgebraicSpace B)
      {U₀ : AlgebraicSpace S} (ι : U₀ ⟶ G.U.left)
      [AlgebraicSpace.IsFirstOrderThickening ι]
      [AlgebraicSpace.Flat G.s.left] [AlgebraicSpace.Flat G.t.left],
      CategoryTheory.Subobject.IsInvariant G.s.left G.t.left (Subobject.mk ι) →
      ∀ {θ1 θ2 : Parameter G ι} {δ1 δ2 : InfinitesimalSection G ι},
        IsPerturbation G ι θ1 δ1 → IsPerturbation G ι θ2 δ2 →
        IsPerturbation G ι (θ1 + θ2) (InfinitesimalSection.comp G ι δ1 δ2))

/- The perturbation correspondence is bijective, with uniqueness in both directions. -/
#check (AlgebraicGeometry.GroupoidAlgebraicSpace.isPerturbation_bijective :
  ∀ {S : Scheme.{u}} [HasPullbacks (AlgebraicSpace S)]
    {B : AlgebraicSpace S} (G : GroupoidAlgebraicSpace B)
    {U₀ : AlgebraicSpace S} (ι : U₀ ⟶ G.U.left)
    [AlgebraicSpace.IsFirstOrderThickening ι],
    CategoryTheory.Subobject.IsInvariant G.s.left G.t.left (Subobject.mk ι) →
    (∀ θ : Parameter G ι, ∃! δ : InfinitesimalSection G ι, IsPerturbation G ι θ δ) ∧
      (∀ δ : InfinitesimalSection G ι, ∃! θ : Parameter G ι, IsPerturbation G ι θ δ))

/- The zero parameter corresponds to the identity section. -/
#check (AlgebraicGeometry.GroupoidAlgebraicSpace.isPerturbation_id :
  ∀ {S : Scheme.{u}} [HasPullbacks (AlgebraicSpace S)]
    {B : AlgebraicSpace S} (G : GroupoidAlgebraicSpace B)
    {U₀ : AlgebraicSpace S} (ι : U₀ ⟶ G.U.left)
    [AlgebraicSpace.IsFirstOrderThickening ι],
    IsPerturbation G ι 0 (InfinitesimalSection.id G ι))

/- The parameter of a composite is the sum of the parameters of its factors. -/
#check (AlgebraicGeometry.GroupoidAlgebraicSpace.eq_add_of_isPerturbation_comp :
  ∀ {S : Scheme.{u}} [HasPullbacks (AlgebraicSpace S)]
    {B : AlgebraicSpace S} (G : GroupoidAlgebraicSpace B)
    {U₀ : AlgebraicSpace S} (ι : U₀ ⟶ G.U.left)
    [AlgebraicSpace.IsFirstOrderThickening ι]
    [AlgebraicSpace.Flat G.s.left] [AlgebraicSpace.Flat G.t.left],
    CategoryTheory.Subobject.IsInvariant G.s.left G.t.left (Subobject.mk ι) →
    ∀ {θ θ1 θ2 : Parameter G ι} {δ1 δ2 : InfinitesimalSection G ι},
      IsPerturbation G ι θ1 δ1 → IsPerturbation G ι θ2 δ2 →
      IsPerturbation G ι θ (InfinitesimalSection.comp G ι δ1 δ2) → θ = θ1 + θ2)
