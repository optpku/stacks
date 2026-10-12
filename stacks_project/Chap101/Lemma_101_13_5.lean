/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import Mathlib.Data.List.TFAE
public import stacks_project.Chap101.Lemma_101_13_5_Local

/-!
# Characterizations of universally closed morphisms of algebraic stacks

Lemma 101.13.5 records that a morphism of algebraic stacks is universally closed
iff this is tested by closed projections after scheme-valued and affine base
change, and by a surjective smooth algebraic-space atlas of the target.
-/

@[expose] public section

open CategoryTheory AlgebraicGeometry
open scoped Bicategory

noncomputable section

universe u

namespace AlgebraicGeometry.AlgebraicStack

namespace UniversallyClosed

variable {S : Scheme.{u}} {X Y : GroupoidsOver S}
variable [AlgebraicStack X] [AlgebraicStack Y] (f : X ⟶ Y)

/-- Lemma 101.13.5: for a morphism `f : X ⟶ Y` of algebraic stacks, the following
are equivalent: `UniversallyClosed f`; for every scheme `Z` and morphism
`Z ⟶ Y` the projection `|Z ×_Y X| ⟶ |Z|` is closed; the same with `Z` affine;
and there exists an algebraic space `V` and a surjective smooth morphism
`V ⟶ Y` such that `V ×_Y X ⟶ V` is universally closed. -/
@[stacks 0CL3]
theorem tfae :
    List.TFAE [UniversallyClosed f, Closed.forallScheme f, Closed.forallAffine f,
      existsSmoothOnTarget f] :=
  sorry

/-- A morphism of algebraic stacks is universally closed iff every
scheme-valued base change has closed projection on points. -/
theorem iff_forallScheme : UniversallyClosed f ↔ Closed.forallScheme f :=
  sorry

/-- A morphism of algebraic stacks is universally closed iff every
affine-scheme-valued base change has closed projection on points. -/
theorem iff_forallAffine : UniversallyClosed f ↔ Closed.forallAffine f :=
  sorry

/-- A morphism of algebraic stacks is universally closed iff some surjective
smooth algebraic-space atlas of the target has universally closed base change. -/
theorem iff_existsSmoothOnTarget :
    UniversallyClosed f ↔ existsSmoothOnTarget f :=
  sorry

end UniversallyClosed

end AlgebraicGeometry.AlgebraicStack
