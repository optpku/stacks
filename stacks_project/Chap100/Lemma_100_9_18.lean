/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.AlgebraicGeometry.AlgebraicStack.Substack.SourceLocus
import StacksCheckRecall

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
open AlgebraicGeometry.AlgebraicStack.Substack
open FiberedCategoryOver.Groupoids
open scoped Bicategory

universe u

/- Lemma 100.9.18. A largest open source substack for a representable
`Q`-morphism exists and remains largest under representable `R`-base change. -/
@[stacks 06M3] #check
  (AlgebraicGeometry.AlgebraicStack.Substack.exists_largestSourceOpen :
    ∀ {S : Scheme.{u}}
    (P Q R : MorphismProperty (AlgebraicSpace S))
    [P.IsStableUnderBaseChange] [Q.IsStableUnderBaseChange]
    [R.IsStableUnderBaseChange]
    [P.IsLocalAtTarget (AlgebraicSpace.fppfPrecoverage S)]
    [Q.IsLocalAtTarget (AlgebraicSpace.fppfPrecoverage S)]
    [R.IsLocalAtTarget (AlgebraicSpace.fppfPrecoverage S)]
    (h_smooth : (@AlgebraicSpace.Smooth S : MorphismProperty (AlgebraicSpace S)) ≤ R)
    (h_largest : ∀ {A B : AlgebraicSpace S} (φ : A ⟶ B),
      Q φ → ∃ W : OpenSubspace A,
        P (W.ι ≫ φ) ∧
          ∀ U : OpenSubspace A, P (U.ι ≫ φ) → U.pointsSet ⊆ W.pointsSet)
    (h_baseChange : ∀ {A B B' : AlgebraicSpace S} (φ : A ⟶ B) (ψ : B' ⟶ B)
      (W : OpenSubspace A),
      Q φ → R ψ →
        (P (W.ι ≫ φ) ∧
          ∀ U : OpenSubspace A, P (U.ι ≫ φ) → U.pointsSet ⊆ W.pointsSet) →
        P ((W.inverseImage (pullback.fst φ ψ)).ι ≫ pullback.snd φ ψ) ∧
          ∀ U : OpenSubspace (pullback φ ψ),
            P (U.ι ≫ pullback.snd φ ψ) →
              U.pointsSet ⊆ (W.inverseImage (pullback.fst φ ψ)).pointsSet)
    {X Y : GroupoidsOver S} [AlgebraicStack X] [AlgebraicStack Y] {f : X ⟶ Y}
    (hf : relativelyRepresentableByAlgebraicSpaces f) (hQ : Groupoids.Hom.has Q f),
    ∃ A : ObjectProperty X.total, IsLargestSourceOpen P f A ∧
      ∀ {Z : GroupoidsOver S} [AlgebraicStack Z] (g : Z ⟶ Y),
        relativelyRepresentableByAlgebraicSpaces g → Groupoids.Hom.has R g →
          IsLargestSourceOpen P (TwoFibreProduct.snd.{u + 1, u, u + 1, u} f g)
            (fun z ↦ A ((toFunctor (TwoFibreProduct.fst.{u + 1, u, u + 1, u} f g)).obj z)))
