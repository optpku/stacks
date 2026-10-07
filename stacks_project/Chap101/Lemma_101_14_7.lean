module

public import Mathlib.Data.List.TFAE
public import stacks_project.Chap101.Lemma_101_14_7_Local

/-!
# Affine characterizations of universally injective morphisms of algebraic stacks

Lemma 101.14.7 records that a morphism of algebraic stacks is universally
injective iff this is tested by universally injective projections after
affine-scheme-valued base change.
-/

@[expose] public section

open CategoryTheory AlgebraicGeometry
open scoped Bicategory

noncomputable section

universe u

namespace AlgebraicGeometry.AlgebraicStack

namespace UniversallyInjective

variable {S : Scheme.{u}} {X Y : GroupoidsOver S}
variable [AlgebraicStack X] [AlgebraicStack Y]

/-- Lemma 101.14.7: for a morphism `f : X ⟶ Y` of algebraic stacks, the following
are equivalent: `UniversallyInjective f`; and for every affine scheme `Z` and
morphism `Z ⟶ Y` the projection `Z ×_Y X ⟶ Z` is universally injective.
The official source lists a third enumerated item `add more here`, which is an
editorial stub and is omitted. -/
@[stacks 0DTN]
theorem tfae (f : X ⟶ Y) :
    List.TFAE [UniversallyInjective f, forallAffine f] :=
  sorry

/-- A morphism of algebraic stacks is universally injective iff every
affine-scheme-valued base change is universally injective. -/
theorem iff_forallAffine (f : X ⟶ Y) :
    UniversallyInjective f ↔ forallAffine f :=
  sorry

end UniversallyInjective

end AlgebraicGeometry.AlgebraicStack
