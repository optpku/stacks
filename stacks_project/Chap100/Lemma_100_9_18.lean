/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import stacks_project.Chap100.Lemma_100_9_18_SourceLocus

/-!
# Largest open source substack for a morphism property

If `P`, `Q`, `R` are fppf local on the target and stable under base change,
smooth morphisms have `R`, and algebraic-space morphisms with `Q` have a
largest `P`-open source subspace stable under `R`-base change, then a morphism
of algebraic stacks representable by algebraic spaces with `Q` has a largest
open source substack with `P`, stable under 2-fibre product along morphisms
with `R`.
-/

@[expose] public section

open CategoryTheory AlgebraicGeometry Limits
open AlgebraicGeometry.AlgebraicSpace
open AlgebraicGeometry.AlgebraicStack
open AlgebraicGeometry.Groupoids.Hom
open FiberedCategoryOver.Groupoids
open scoped Bicategory

noncomputable section

universe u

namespace AlgebraicGeometry.Groupoids.Hom

/-- Lemma 100.9.18 (1): Let `P`, `Q`, `R` be properties of morphisms of
algebraic spaces that are fppf local on the target and stable under arbitrary
base change, with `Smooth ≤ R`. Assume every algebraic-space morphism with `Q`
has a largest open source subspace on which the restriction has `P`, and that
this locus is stable under `R`-base change. If `f : X ⟶ Y` is a morphism of
algebraic stacks representable by algebraic spaces and `has Q f`, then
`sourceLocus P f` is a largest open substack of `X` on which `f` has `P`. -/
@[stacks 06M3]
theorem sourceLocus_isLargest {S : Scheme.{u}}
    (P Q R : MorphismProperty (AlgebraicSpace S))
    [P.IsStableUnderBaseChange] [Q.IsStableUnderBaseChange]
    [R.IsStableUnderBaseChange]
    [P.IsLocalAtTarget (AlgebraicSpace.fppfPrecoverage S)]
    [Q.IsLocalAtTarget (AlgebraicSpace.fppfPrecoverage S)]
    [R.IsLocalAtTarget (AlgebraicSpace.fppfPrecoverage S)]
    (h_smooth : (@AlgebraicSpace.Smooth S : MorphismProperty (AlgebraicSpace S)) ≤ R)
    (h_largest : ∀ {A B : AlgebraicSpace S} (φ : A ⟶ B),
      Q φ → ∃ W : OpenSubspace A, IsLargestSourceOpen P φ W)
    (h_baseChange : ∀ {A B B' : AlgebraicSpace S} (φ : A ⟶ B) (ψ : B' ⟶ B)
      (W : OpenSubspace A),
      Q φ → R ψ → IsLargestSourceOpen P φ W →
        IsLargestSourceOpen P (pullback.snd φ ψ)
          (W.inverseImage (pullback.fst φ ψ)))
    {X Y : GroupoidsOver S} [AlgebraicStack X] [AlgebraicStack Y] {f : X ⟶ Y}
    (hf : relativelyRepresentableByAlgebraicSpaces f) (hQ : has Q f) :
    IsLargestSourceOpenStack P f (sourceLocus P f) :=
  sorry

/-- Lemma 100.9.18 (2): In the setup of Lemma 100.9.18 (1), if
`g : Z ⟶ Y` is representable by algebraic spaces and `has R g`, then
`(sourceLocus P f).pullback f g` is a largest open substack of
`Z ×_Y X` on which `id_Z × f = TwoFibreProduct.snd f g` has `P`. -/
@[stacks 06M3]
theorem sourceLocus_pullback {S : Scheme.{u}}
    (P Q R : MorphismProperty (AlgebraicSpace S))
    [P.IsStableUnderBaseChange] [Q.IsStableUnderBaseChange]
    [R.IsStableUnderBaseChange]
    [P.IsLocalAtTarget (AlgebraicSpace.fppfPrecoverage S)]
    [Q.IsLocalAtTarget (AlgebraicSpace.fppfPrecoverage S)]
    [R.IsLocalAtTarget (AlgebraicSpace.fppfPrecoverage S)]
    (h_smooth : (@AlgebraicSpace.Smooth S : MorphismProperty (AlgebraicSpace S)) ≤ R)
    (h_largest : ∀ {A B : AlgebraicSpace S} (φ : A ⟶ B),
      Q φ → ∃ W : OpenSubspace A, IsLargestSourceOpen P φ W)
    (h_baseChange : ∀ {A B B' : AlgebraicSpace S} (φ : A ⟶ B) (ψ : B' ⟶ B)
      (W : OpenSubspace A),
      Q φ → R ψ → IsLargestSourceOpen P φ W →
        IsLargestSourceOpen P (pullback.snd φ ψ)
          (W.inverseImage (pullback.fst φ ψ)))
    {X Y Z : GroupoidsOver S} [AlgebraicStack X] [AlgebraicStack Y]
    [AlgebraicStack Z] {f : X ⟶ Y}
    (hf : relativelyRepresentableByAlgebraicSpaces f) (hQ : has Q f)
    {g : Z ⟶ Y} (hg : relativelyRepresentableByAlgebraicSpaces g)
    (hR : has R g) :
    IsLargestSourceOpenStack P (TwoFibreProduct.snd.{u + 1, u, u + 1, u} f g)
      ((sourceLocus P f).pullback f g) :=
  sorry

end AlgebraicGeometry.Groupoids.Hom
