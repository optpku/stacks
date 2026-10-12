/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import Mathlib.Data.List.TFAE
public import stacks_project.Chap101.Definition_101_7_2_QuasiCompact
public import stacks_project.Chap102.Lemma_102_7_2_Tests

/-!
# Testing universal closedness of quasi-compact morphisms of algebraic stacks

Lemma 102.7.2 records that a quasi-compact morphism of algebraic stacks is
universally closed iff this is tested by closed projections after affine
locally-of-finite-presentation base change, and iff some surjective smooth
scheme atlas of the target has closed affine-space product projections.
-/

@[expose] public section

open CategoryTheory AlgebraicGeometry Bicategory
open scoped Bicategory AlgebraicGeometry

universe u

namespace AlgebraicGeometry.AlgebraicStack

namespace UniversallyClosed

variable {S : Scheme.{u}} {X Y : GroupoidsOver S}
variable [AlgebraicStack X] [AlgebraicStack Y] (f : X ⟶ Y) [QuasiCompact f]

/-- Lemma 102.7.2: for a quasi-compact morphism `f : 𝒳 ⟶ 𝒴` of algebraic stacks
over a scheme `S`, the following are equivalent: `UniversallyClosed f`; for
every morphism `Z ⟶ 𝒴` which is locally of finite presentation with `Z` an
affine scheme, the projection `|𝒳 ×_𝒴 Z| ⟶ |Z|` is closed; and there exists a
scheme `V` and a surjective smooth morphism `V ⟶ 𝒴` such that
`|𝔸(n) × (𝒳 ×_𝒴 V)| ⟶ |𝔸(n) × V|` is closed for every `n : ℕ`. -/
@[stacks 0H2A]
theorem tfae_quasiCompact :
    List.TFAE [UniversallyClosed f, Closed.forallAffineLocallyOfFinitePresentation f,
      Closed.existsSmoothAffineSpace f] := sorry

/-- A quasi-compact morphism of algebraic stacks is universally closed iff every
affine locally-of-finite-presentation base change has closed projection on
points. -/
theorem iff_forallAffineLocallyOfFinitePresentation :
    UniversallyClosed f ↔ Closed.forallAffineLocallyOfFinitePresentation f := sorry

/-- A quasi-compact morphism of algebraic stacks is universally closed iff some
surjective smooth scheme atlas of the target has closed affine-space product
projections. -/
theorem iff_existsSmoothAffineSpace :
    UniversallyClosed f ↔ Closed.existsSmoothAffineSpace f := sorry

end UniversallyClosed

end AlgebraicGeometry.AlgebraicStack
