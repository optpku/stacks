/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import Mathlib.Data.List.TFAE
public import stacks_project.Chap67.Definition_67_8_2_QuasiCompact
public import stacks_project.Chap70.Lemma_70_20_2_Tests

/-!
# Testing universal closedness of quasi-compact morphisms of algebraic spaces

Lemma 70.20.2 records that a quasi-compact morphism of algebraic spaces is
universally closed iff this is tested by closed projections after base change
locally of finite presentation, and iff some surjective étale scheme atlas of
the target has closed affine-space product projections.
-/

@[expose] public section

open CategoryTheory AlgebraicGeometry Limits

universe u

namespace AlgebraicGeometry.AlgebraicSpace

namespace UniversallyClosed

variable {S : Scheme.{u}} {X Y : AlgebraicSpace S} (f : X ⟶ Y) [QuasiCompact f]

/-- Lemma 70.20.2: for a quasi-compact morphism `f : X ⟶ Y` of algebraic spaces
over a scheme `S`, the following are equivalent: `UniversallyClosed f`; every
base change of `f` along a morphism locally of finite presentation has closed
projection on points; and there exists a scheme `V` and a surjective étale
morphism `V ⟶ Y` such that each affine-space product of a pullback of `f` along
`𝔸(n; V) ⟶ Y` is closed on points for every `n : ℕ`. -/
@[stacks 0CM9]
theorem tfae_quasiCompact :
    List.TFAE [UniversallyClosed f, Closed.forallLocallyOfFinitePresentation f,
      Closed.existsEtaleAffineSpace f] := sorry

/-- A quasi-compact morphism of algebraic spaces is universally closed iff every
base change along a morphism locally of finite presentation has closed
projection on points. -/
theorem iff_forallLocallyOfFinitePresentation :
    UniversallyClosed f ↔ Closed.forallLocallyOfFinitePresentation f := sorry

/-- A quasi-compact morphism of algebraic spaces is universally closed iff some
surjective étale scheme atlas of the target has closed affine-space product
projections. -/
theorem iff_existsEtaleAffineSpace :
    UniversallyClosed f ↔ Closed.existsEtaleAffineSpace f := sorry

end UniversallyClosed

end AlgebraicGeometry.AlgebraicSpace
