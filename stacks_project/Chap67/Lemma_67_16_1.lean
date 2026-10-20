/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.AlgebraicGeometry.AlgebraicSpace.SchemeTheoreticImage
import StacksCheckRecall

/-!
# Existence of scheme-theoretic images of morphisms of algebraic spaces

Every morphism of algebraic spaces over a scheme has a least closed subspace of
its target through which it factors.
-/

@[expose] public section

open CategoryTheory AlgebraicGeometry

universe u

/- Lemma 67.16.1: Let `S` be a scheme. Let `f : X ⟶ Y` be a morphism of
algebraic spaces over `S`. There exists a closed subspace `Z ⊂ Y` such that
`f` factors through `Z` and such that for any other closed subspace `Z' ⊂ Y`
through which `f` factors we have `Z ⊂ Z'`. -/
@[stacks 082X] #check
  (AlgebraicGeometry.AlgebraicSpace.IsSchemeTheoreticImage.exists_schemeTheoreticImage :
    ∀ {S : Scheme.{u}} {X Y : AlgebraicSpace S} (f : X ⟶ Y),
      ∃ (Z : AlgebraicSpace S) (toImage : X ⟶ Z) (ι : Z ⟶ Y),
        AlgebraicGeometry.AlgebraicSpace.IsSchemeTheoreticImage f toImage ι)

/- There exists a least closed subspace of `Y` through which `f` factors: any
other such closed subspace admits a comparison over `Y`. -/
#check
  (AlgebraicGeometry.AlgebraicSpace.IsSchemeTheoreticImage.exists_least_closedSubspace :
    ∀ {S : Scheme.{u}} {X Y : AlgebraicSpace S} (f : X ⟶ Y),
      ∃ Z : AlgebraicSpace.ClosedSubspace Y,
        (∃ toZ : X ⟶ Z.X, toZ ≫ Z.ι = f) ∧
          ∀ Z' : AlgebraicSpace.ClosedSubspace Y,
            (∃ toZ' : X ⟶ Z'.X, toZ' ≫ Z'.ι = f) →
              ∃ k : Z.X ⟶ Z'.X, k ≫ Z'.ι = Z.ι)

/- A least closed-subspace factorization of `f` is a scheme-theoretic image
factorization. Uniqueness of the comparison follows from closed immersions
being monomorphisms. -/
#check
  (AlgebraicGeometry.AlgebraicSpace.IsSchemeTheoreticImage.of_isLeast_closedSubspace :
    ∀ {S : Scheme.{u}} {X Y : AlgebraicSpace S} (f : X ⟶ Y)
      (Z : AlgebraicSpace.ClosedSubspace Y) (toImage : X ⟶ Z.X),
      toImage ≫ Z.ι = f →
        (∀ Z' : AlgebraicSpace.ClosedSubspace Y,
          (∃ toZ' : X ⟶ Z'.X, toZ' ≫ Z'.ι = f) →
            ∃ k : Z.X ⟶ Z'.X, k ≫ Z'.ι = Z.ι) →
          AlgebraicGeometry.AlgebraicSpace.IsSchemeTheoreticImage f toImage Z.ι)
