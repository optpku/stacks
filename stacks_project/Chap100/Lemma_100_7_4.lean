module

public import ReasLib.AlgebraicGeometry.AlgebraicStack.GermProperty
import StacksCheckRecall

/-!
# Smooth-local germ properties of algebraic stacks at a point

A property of scheme germs that is smooth local may be tested on any, or some,
smooth morphism to an algebraic stack from a scheme or from an algebraic space
through a fixed point.
-/

@[expose] public section

open CategoryTheory AlgebraicGeometry
open scoped Bicategory

universe u

namespace AlgebraicGeometry.AlgebraicStack

/- Lemma 100.7.4: let `P` be a smooth-local property of scheme germs, let `X`
be an algebraic stack, and let `x` be a point of `X`. The following four conditions
are equivalent: `P` holds at every smooth scheme chart through `x`; it holds at
some smooth scheme chart through `x`; every smooth algebraic-space chart through
`x` has property `P` at its source point; and some smooth algebraic-space chart
through `x` has property `P` at its source point. If `X` is representable by a
scheme, these conditions recover `P` at the corresponding scheme point. If `X`
is an algebraic space, they recover its étale-local germ property at `x`. -/
@[stacks 04YI] #check (AlgebraicGeometry.AlgebraicStack.forallSmoothAt_iff_existsSmoothAt :
  ∀ {S : Scheme.{u}}
    (P : GermProperty.{u}) (hP : P.IsSmoothLocal)
    (X : GroupoidsOver S) [AlgebraicStack X] (x : Points X),
    forallSmoothAt P X x ↔ existsSmoothAt P X x)

/- let `P` be a smooth-local property of scheme germs, let `X`
be an algebraic stack, and let `x` be a point of `X`. There exists a smooth
scheme chart through `x` with property `P` if and only if there exists a smooth
algebraic-space chart through `x` on which the source has property `P`. -/
#check (AlgebraicGeometry.AlgebraicStack.existsSmoothAt_iff_existsSmoothSpaceAt :
  ∀ {S : Scheme.{u}}
    (P : GermProperty.{u}) (hP : P.IsSmoothLocal)
    (X : GroupoidsOver S) [AlgebraicStack X] (x : Points X),
    existsSmoothAt P X x ↔ existsSmoothSpaceAt P X x)

/- let `P` be a smooth-local property of scheme germs, let `X`
be an algebraic stack, and let `x` be a point of `X`. There exists a smooth
algebraic-space chart through `x` on which the source has property `P` if and
only if every smooth algebraic-space chart through `x` has property `P` on the
source. -/
#check (AlgebraicGeometry.AlgebraicStack.existsSmoothSpaceAt_iff_forallSmoothSpaceAt :
  ∀ {S : Scheme.{u}}
    (P : GermProperty.{u}) (hP : P.IsSmoothLocal)
    (X : GroupoidsOver S) [AlgebraicStack X] (x : Points X),
    existsSmoothSpaceAt P X x ↔ forallSmoothSpaceAt P X x)

/- if `X` is a scheme `U` over `S` and `u` is a point of `U`,
then `existsSmoothAt P (GroupoidsOver.slice U) (Points.ofSlice u)` is equivalent
to `P U.left u`. -/
#check (AlgebraicGeometry.AlgebraicStack.existsSmoothAt_slice :
  ∀ {S : Scheme.{u}} (P : GermProperty.{u})
    (hP : P.IsSmoothLocal) (U : Over S) (u : U.left),
    existsSmoothAt P (GroupoidsOver.slice U) (Points.ofSlice u) ↔ P U.left u)

/- if `X` is an algebraic space `F` over `S` and `x` is a
point of `F`, then `existsSmoothAt P F.toGroupoids (Points.ofAlgebraicSpace x)`
is equivalent to `F` having property `P` at `x`. -/
#check (AlgebraicGeometry.AlgebraicStack.existsSmoothAt_toGroupoids :
  ∀ {S : Scheme.{u}} (P : GermProperty.{u})
    (hP : P.IsSmoothLocal) (F : AlgebraicSpace S) (x : AlgebraicSpace.Points F),
    existsSmoothAt P F.toGroupoids (Points.ofAlgebraicSpace x) ↔
      AlgebraicSpace.hasEtaleLocalAt P hP.isEtaleLocal F x)

/- If `U` is a scheme over `S` and `u` is a point of `U`, then every smooth
scheme chart of `GroupoidsOver.slice U` through `ofSlice u` has property `P` if
and only if `P` holds at `(U.left, u)`. -/
#check (AlgebraicGeometry.AlgebraicStack.forallSmoothAt_slice :
  ∀ {S : Scheme.{u}} (P : GermProperty.{u})
    (hP : P.IsSmoothLocal) (U : Over S) (u : U.left),
    forallSmoothAt P (GroupoidsOver.slice U) (Points.ofSlice u) ↔ P U.left u)

/- The smooth-local germ criterion at a point transports along an equivalence
to a scheme slice. -/
#check (AlgebraicGeometry.AlgebraicStack.existsSmoothAt_equivalence :
  ∀ {S : Scheme.{u}} (P : GermProperty.{u})
    (hP : P.IsSmoothLocal) {X : GroupoidsOver S} [AlgebraicStack X] {U : Over S}
    (e : X ≌ GroupoidsOver.slice U) (x : Points X),
    existsSmoothAt P X x ↔
      existsSmoothAt P (GroupoidsOver.slice U) (Points.map e.hom x))

end AlgebraicGeometry.AlgebraicStack
