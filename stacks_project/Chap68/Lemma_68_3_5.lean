/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import Mathlib.AlgebraicGeometry.Morphisms.Flat
public import stacks_project.Chap68.Definition_68_3_1_FiberDegree

/-!
# Cancellation of universally bounded fibres along flat surjective precomposition

Universally bounded fibres of a morphism from a scheme to an algebraic space
descend along precomposition by a flat surjective morphism of schemes over `S`.
-/

@[expose] public section

open CategoryTheory AlgebraicGeometry

universe u

namespace AlgebraicGeometry.AlgebraicSpace

/-- Lemma 68.3.5: Let `S` be a scheme. Let `X` be an algebraic space over `S`.
Consider a commutative triangle of morphisms of schemes `U`, `V` to `X`, with
`f : U ⟶ V` over `S` and `h : ofOver V ⟶ X`, so that `g = ofOverMap f ≫ h`.
If `g` has universally bounded fibres and `f` is flat and surjective, then `h`
has universally bounded fibres. -/
@[stacks 03JP]
theorem universallyBoundedFibres_of_comp_of_flat_of_surjective
    {S : Scheme.{u}} {X : AlgebraicSpace S} {U V : Over S}
    (f : U ⟶ V) (h : ofOver V ⟶ X)
    [AlgebraicGeometry.Flat f.left] [AlgebraicGeometry.Surjective f.left]
    (hg : universallyBoundedFibres (ofOverMap f ≫ h)) :
    universallyBoundedFibres h :=
  sorry

/-- A fixed numerical bound on fibre degrees of `ofOverMap f ≫ h` also bounds
the fibre degrees of `h`, when `f.left` is flat and surjective. -/
theorem degreesOfFibresBoundedBy_of_comp_of_flat_of_surjective
    {S : Scheme.{u}} {X : AlgebraicSpace S} {U V : Over S}
    (f : U ⟶ V) (h : ofOver V ⟶ X)
    [AlgebraicGeometry.Flat f.left] [AlgebraicGeometry.Surjective f.left]
    {n : ℕ} (hg : degreesOfFibresBoundedBy (ofOverMap f ≫ h) n) :
    degreesOfFibresBoundedBy h n :=
  sorry

end AlgebraicGeometry.AlgebraicSpace
