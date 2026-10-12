/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import stacks_project.Chap67.Lemma_67_30_5_Flat
public import stacks_project.Chap79.«79_5_1_1»

/-!
# Composition of infinitesimal source sections is addition of parameters

The 79.5.1.1 correspondence sending a parameter `θ` to the infinitesimal source
section `δ = θ · e` intertwines addition of parameters with composition in `Γ₀`.
-/

@[expose] public section

open CategoryTheory AlgebraicGeometry Limits
open CategoryTheory.Preadditive

noncomputable section

universe u

namespace AlgebraicGeometry.GroupoidAlgebraicSpace

variable {S : Scheme.{u}} {B : AlgebraicSpace S} (G : GroupoidAlgebraicSpace B)
variable {U₀ : AlgebraicSpace S} (ι : U₀ ⟶ G.U.left)

/-- The restriction of the ambient composite of two infinitesimal source
sections to `U₀` is the restricted identity. -/
theorem InfinitesimalSection.comp_restrict
    [AlgebraicSpace.IsFirstOrderThickening ι]
    (δ1 δ2 : InfinitesimalSection G ι) :
    identityRestrict G ι ≫ arrowι G ι =
      ι ≫ (Section.comp G (InfinitesimalSection.toSection G ι δ1)
          (InfinitesimalSection.toSection G ι δ2)).arrow.left :=
  sorry

/-- Composition of infinitesimal source sections, obtained from the ambient
groupoid composition of the underlying source sections. -/
def InfinitesimalSection.comp [AlgebraicSpace.IsFirstOrderThickening ι]
    (δ1 δ2 : InfinitesimalSection G ι) : InfinitesimalSection G ι :=
  let δ := Section.comp G (InfinitesimalSection.toSection G ι δ1)
    (InfinitesimalSection.toSection G ι δ2)
  InfinitesimalSection.of G ι δ.arrow δ.source
    (InfinitesimalSection.comp_restrict G ι δ1 δ2)

/-- Unfolding of `InfinitesimalSection.comp` on underlying arrows. -/
theorem InfinitesimalSection.comp_arrow
    [AlgebraicSpace.IsFirstOrderThickening ι]
    (δ1 δ2 : InfinitesimalSection G ι) :
    (InfinitesimalSection.comp G ι δ1 δ2).arrow =
      (Section.comp G (InfinitesimalSection.toSection G ι δ1)
          (InfinitesimalSection.toSection G ι δ2)).arrow :=
  sorry

/-- Lemma 79.5.2: The bijection 79.5.1.1 is an isomorphism of groups: if
infinitesimal source sections `δ1`, `δ2` correspond to parameters `θ1`, `θ2`,
then their composite in `Γ₀` corresponds to `θ1 + θ2`. -/
@[stacks 0CKF]
theorem isPerturbation_comp [AlgebraicSpace.IsFirstOrderThickening ι]
    [AlgebraicSpace.Flat G.s.left] [AlgebraicSpace.Flat G.t.left]
    (h_invariant : G.toPreRelation.IsInvariant (Subobject.mk ι))
    {θ1 θ2 : Parameter G ι} {δ1 δ2 : InfinitesimalSection G ι}
    (h1 : IsPerturbation G ι θ1 δ1) (h2 : IsPerturbation G ι θ2 δ2) :
    IsPerturbation G ι (θ1 + θ2) (InfinitesimalSection.comp G ι δ1 δ2) :=
  sorry

/-- The zero parameter corresponds to the identity infinitesimal source section. -/
theorem isPerturbation_id [AlgebraicSpace.IsFirstOrderThickening ι] :
    IsPerturbation G ι 0 (InfinitesimalSection.id G ι) :=
  sorry

/-- If infinitesimal source sections corresponding to `θ1` and `θ2` have
composite corresponding to `θ`, then `θ = θ1 + θ2`. -/
theorem eq_add_of_isPerturbation_comp
    [AlgebraicSpace.IsFirstOrderThickening ι]
    [AlgebraicSpace.Flat G.s.left] [AlgebraicSpace.Flat G.t.left]
    (h_invariant : G.toPreRelation.IsInvariant (Subobject.mk ι))
    {θ θ1 θ2 : Parameter G ι} {δ1 δ2 : InfinitesimalSection G ι}
    (h1 : IsPerturbation G ι θ1 δ1) (h2 : IsPerturbation G ι θ2 δ2)
    (h : IsPerturbation G ι θ (InfinitesimalSection.comp G ι δ1 δ2)) :
    θ = θ1 + θ2 :=
  sorry


end AlgebraicGeometry.GroupoidAlgebraicSpace
