/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import Mathlib.Data.List.TFAE
public import stacks_project.Chap67.Definition_67_40_1_Proper
public import stacks_project.Chap70.Lemma_70_20_2_Tests

/-!
# Testing properness of separated finite-type morphisms of algebraic spaces

Lemma 70.20.3 records that a separated finite-type morphism of algebraic spaces
is proper iff this is tested by closed projections after base change locally of
finite presentation, and iff some surjective étale scheme atlas of the target
has closed affine-space product projections.
-/

@[expose] public section

open CategoryTheory AlgebraicGeometry Limits

universe u

namespace AlgebraicGeometry.AlgebraicSpace

namespace Proper

variable {S : Scheme.{u}} {X Y : AlgebraicSpace S} (f : X ⟶ Y) [Separated f] [FiniteType f]

/-- Lemma 70.20.3: for a separated finite-type morphism `f : X ⟶ Y` of algebraic
spaces over a scheme `S`, the following are equivalent: `Proper f`; every
base change of `f` along a morphism locally of finite presentation has closed
projection on points; and there exists a scheme `V` and a surjective étale
morphism `V ⟶ Y` such that each affine-space product of a pullback of `f` along
`𝔸(n; V) ⟶ Y` is closed on points for every `n : ℕ`. -/
@[stacks 0CMA]
theorem tfae_separatedFiniteType :
    List.TFAE [Proper f, Closed.forallLocallyOfFinitePresentation f,
      Closed.existsEtaleAffineSpace f] := sorry

/-- A separated finite-type morphism of algebraic spaces is proper iff every
base change along a morphism locally of finite presentation has closed
projection on points. -/
theorem iff_forallLocallyOfFinitePresentation :
    Proper f ↔ Closed.forallLocallyOfFinitePresentation f := sorry

/-- A separated finite-type morphism of algebraic spaces is proper iff some
surjective étale scheme atlas of the target has closed affine-space product
projections. -/
theorem iff_existsEtaleAffineSpace :
    Proper f ↔ Closed.existsEtaleAffineSpace f := sorry

end Proper

end AlgebraicGeometry.AlgebraicSpace
