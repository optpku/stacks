/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import stacks_project.Chap67.Lemma_67_16_6_SchemeTheoreticImage
public import stacks_project.Chap65.Definition_65_12_1_Subspace

/-!
# Existence of scheme-theoretic images of morphisms of algebraic spaces

Every morphism of algebraic spaces over a scheme has a least closed subspace of
its target through which it factors.
-/

@[expose] public section

open CategoryTheory AlgebraicGeometry

universe u

namespace AlgebraicGeometry.AlgebraicSpace.IsSchemeTheoreticImage

/-- Lemma 67.16.1: Let `S` be a scheme. Let `f : X ⟶ Y` be a morphism of
algebraic spaces over `S`. There exists a closed subspace `Z ⊂ Y` such that
`f` factors through `Z` and such that for any other closed subspace `Z' ⊂ Y`
through which `f` factors we have `Z ⊂ Z'`. -/
@[stacks 082X]
theorem exists_schemeTheoreticImage {S : Scheme.{u}} {X Y : AlgebraicSpace S} (f : X ⟶ Y) :
    ∃ (Z : AlgebraicSpace S) (toImage : X ⟶ Z) (ι : Z ⟶ Y),
      IsSchemeTheoreticImage f toImage ι := sorry

/-- There exists a least closed subspace of `Y` through which `f` factors: any
other such closed subspace admits a comparison over `Y`. -/
theorem exists_least_closedSubspace {S : Scheme.{u}} {X Y : AlgebraicSpace S}
    (f : X ⟶ Y) :
    ∃ Z : ClosedSubspace Y,
      (∃ toZ : X ⟶ Z.X, toZ ≫ Z.ι = f) ∧
        ∀ Z' : ClosedSubspace Y, (∃ toZ' : X ⟶ Z'.X, toZ' ≫ Z'.ι = f) →
          ∃ k : Z.X ⟶ Z'.X, k ≫ Z'.ι = Z.ι := sorry

/-- A least closed-subspace factorization of `f` is a scheme-theoretic image
factorization. Uniqueness of the comparison follows from closed immersions
being monomorphisms. -/
theorem of_isLeast_closedSubspace {S : Scheme.{u}} {X Y : AlgebraicSpace S}
    (f : X ⟶ Y) (Z : ClosedSubspace Y) (toImage : X ⟶ Z.X)
    (hfac : toImage ≫ Z.ι = f)
    (hleast : ∀ Z' : ClosedSubspace Y,
      (∃ toZ' : X ⟶ Z'.X, toZ' ≫ Z'.ι = f) →
        ∃ k : Z.X ⟶ Z'.X, k ≫ Z'.ι = Z.ι) :
    IsSchemeTheoreticImage f toImage Z.ι := sorry

end AlgebraicGeometry.AlgebraicSpace.IsSchemeTheoreticImage
