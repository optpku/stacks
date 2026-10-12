/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import stacks_project.Chap100.Lemma_100_7_4

/-!
# Smooth-local germ properties of algebraic stacks at a point

A smooth-local property of scheme germs descends to an algebraic stack at a
point by testing it on a smooth scheme chart through that point.
-/

@[expose] public section

open CategoryTheory AlgebraicGeometry
open scoped Bicategory

noncomputable section

universe u

namespace AlgebraicGeometry.AlgebraicStack

/-- An algebraic stack `X` has a smooth-local germ property `P` at a point `x`
when some smooth scheme chart through `x` has property `P`. -/
def hasSmoothLocalAt {S : Scheme.{u}} (P : GermProperty.{u})
    (hP : P.IsSmoothLocal) (X : GroupoidsOver S) [AlgebraicStack X]
    (x : Points X) : Prop :=
  existsSmoothAt P X x

/-- `hasSmoothLocalAt P hP X x` is the existence of a smooth scheme chart
through `x` on which `P` holds. -/
theorem hasSmoothLocalAt_def {S : Scheme.{u}} (P : GermProperty.{u})
    (hP : P.IsSmoothLocal) (X : GroupoidsOver S) [AlgebraicStack X]
    (x : Points X) :
    hasSmoothLocalAt P hP X x ↔ existsSmoothAt P X x :=
  Iff.rfl

namespace hasSmoothLocalAt

/-- A smooth morphism from a scheme through `x` on which `P` holds witnesses
`hasSmoothLocalAt P hP X x`. -/
theorem of {S : Scheme.{u}} {P : GermProperty.{u}} (hP : P.IsSmoothLocal)
    {X : GroupoidsOver S} [AlgebraicStack X] {x : Points X} {U : Over S}
    (p : GroupoidsOver.slice U ⟶ X) (u : U.left) [Groupoids.Hom.Smooth p]
    (hx : Points.mapSlice p u = x) (hPu : P U.left u) :
    hasSmoothLocalAt P hP X x :=
  existsSmoothAt.of p u hx hPu

/-- An algebraic stack satisfying `hasSmoothLocalAt P hP X x` admits a smooth
scheme chart through `x` on which `P` holds. -/
theorem spec {S : Scheme.{u}} {P : GermProperty.{u}} (hP : P.IsSmoothLocal)
    {X : GroupoidsOver S} [AlgebraicStack X] {x : Points X}
    (h : hasSmoothLocalAt P hP X x) :
    ∃ (U : Over S) (p : GroupoidsOver.slice U ⟶ X) (u : U.left),
      Groupoids.Hom.Smooth p ∧ Points.mapSlice p u = x ∧ P U.left u :=
  h

end hasSmoothLocalAt

/-- `X` has a smooth-local germ property `P` at `x` if and only if every smooth
morphism from a scheme through `x` has property `P` at the source point. -/
theorem hasSmoothLocalAt_iff_forallSmoothAt {S : Scheme.{u}}
    (P : GermProperty.{u}) (hP : P.IsSmoothLocal) (X : GroupoidsOver S)
    [AlgebraicStack X] (x : Points X) :
    hasSmoothLocalAt P hP X x ↔ forallSmoothAt P X x :=
  (forallSmoothAt_iff_existsSmoothAt P hP X x).symm

/-- `X` has a smooth-local germ property `P` at `x` if and only if some smooth
algebraic-space chart through `x` has property `P` at the source point. -/
theorem hasSmoothLocalAt_iff_existsSmoothSpaceAt {S : Scheme.{u}}
    (P : GermProperty.{u}) (hP : P.IsSmoothLocal) (X : GroupoidsOver S)
    [AlgebraicStack X] (x : Points X) :
    hasSmoothLocalAt P hP X x ↔ existsSmoothSpaceAt P X x :=
  existsSmoothAt_iff_existsSmoothSpaceAt P hP X x

/-- `X` has a smooth-local germ property `P` at `x` if and only if every smooth
morphism from an algebraic space through `x` has property `P` at the source
point. -/
theorem hasSmoothLocalAt_iff_forallSmoothSpaceAt {S : Scheme.{u}}
    (P : GermProperty.{u}) (hP : P.IsSmoothLocal) (X : GroupoidsOver S)
    [AlgebraicStack X] (x : Points X) :
    hasSmoothLocalAt P hP X x ↔ forallSmoothSpaceAt P X x :=
  (existsSmoothAt_iff_existsSmoothSpaceAt P hP X x).trans
    (existsSmoothSpaceAt_iff_forallSmoothSpaceAt P hP X x)

/-- If `X` is a scheme `U` over `S` and `u` is a point of `U`, then
`hasSmoothLocalAt P` on the slice of `U` at `ofSlice u` is equivalent to
`P U.left u`. -/
theorem hasSmoothLocalAt_slice {S : Scheme.{u}} (P : GermProperty.{u})
    (hP : P.IsSmoothLocal) (U : Over S) (u : U.left) :
    hasSmoothLocalAt P hP (GroupoidsOver.slice U) (Points.ofSlice u) ↔
      P U.left u :=
  existsSmoothAt_slice P hP U u

/-- If `X` is an algebraic space `F` over `S` and `x` is a point of `F`, then
`hasSmoothLocalAt P` on `F.toGroupoids` at `ofAlgebraicSpace x` is equivalent
to `F` having property `P` at `x`. -/
theorem hasSmoothLocalAt_toGroupoids {S : Scheme.{u}} (P : GermProperty.{u})
    (hP : P.IsSmoothLocal) (F : AlgebraicSpace S) (x : AlgebraicSpace.Points F) :
    hasSmoothLocalAt P hP F.toGroupoids (Points.ofAlgebraicSpace x) ↔
      AlgebraicSpace.hasEtaleLocalAt P hP.isEtaleLocal F x :=
  existsSmoothAt_toGroupoids P hP F x

end AlgebraicGeometry.AlgebraicStack
