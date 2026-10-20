/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.AlgebraicGeometry.Scheme.GermProperty
public import ReasLib.AlgebraicGeometry.AlgebraicSpace.GermProperty
public import ReasLib.AlgebraicGeometry.AlgebraicStack.Points.Comparison

/-!
# Smooth-local germ transfer at a point of an algebraic stack

A smooth-local property of scheme germs may be tested on smooth morphisms from
schemes or algebraic spaces through a fixed point of an algebraic stack: the
“for any chart” and “for some chart” conditions are the basic predicates.
-/

@[expose] public section

open CategoryTheory AlgebraicGeometry
open scoped Bicategory

noncomputable section

universe u

namespace AlgebraicGeometry.AlgebraicStack

/-- There exists a scheme `U` over `S` and a smooth morphism `p : slice U ⟶ X`
together with a point `u : U.left` such that `Points.mapSlice p u = x` and `P`
holds at `(U.left, u)`. -/
def existsSmoothAt {S : Scheme.{u}} (P : GermProperty.{u})
    (X : GroupoidsOver S) [AlgebraicStack X] (x : Points X) : Prop :=
  ∃ (U : Over S) (p : GroupoidsOver.slice U ⟶ X) (u : U.left),
    Groupoids.Hom.Smooth p ∧ Points.mapSlice p u = x ∧ P U.left u

/-- `existsSmoothAt P X x` is the existence of a smooth scheme chart through `x`
on which `P` holds. -/
theorem existsSmoothAt_def {S : Scheme.{u}} (P : GermProperty.{u})
    (X : GroupoidsOver S) [AlgebraicStack X] (x : Points X) :
    existsSmoothAt P X x ↔
      ∃ (U : Over S) (p : GroupoidsOver.slice U ⟶ X) (u : U.left),
        Groupoids.Hom.Smooth p ∧ Points.mapSlice p u = x ∧ P U.left u :=
  Iff.rfl

namespace existsSmoothAt

/-- A smooth morphism from a scheme through `x` on which `P` holds witnesses
`existsSmoothAt P X x`. -/
theorem of {S : Scheme.{u}} {P : GermProperty.{u}} {X : GroupoidsOver S}
    [AlgebraicStack X] {x : Points X} {U : Over S}
    (p : GroupoidsOver.slice U ⟶ X) (u : U.left) [Groupoids.Hom.Smooth p]
    (hx : Points.mapSlice p u = x) (hP : P U.left u) :
    existsSmoothAt P X x :=
  ⟨U, p, u, inferInstance, hx, hP⟩

/-- An algebraic stack satisfying `existsSmoothAt P X x` admits a smooth scheme
chart through `x` on which `P` holds. -/
theorem spec {S : Scheme.{u}} {P : GermProperty.{u}} {X : GroupoidsOver S}
    [AlgebraicStack X] {x : Points X} (h : existsSmoothAt P X x) :
    ∃ (U : Over S) (p : GroupoidsOver.slice U ⟶ X) (u : U.left),
      Groupoids.Hom.Smooth p ∧ Points.mapSlice p u = x ∧ P U.left u :=
  h

end existsSmoothAt

/-- Every smooth morphism `p : slice U ⟶ X` from a scheme over `S` and every
point `u : U.left` with `Points.mapSlice p u = x` has `P` at `(U.left, u)`. -/
def forallSmoothAt {S : Scheme.{u}} (P : GermProperty.{u})
    (X : GroupoidsOver S) [AlgebraicStack X] (x : Points X) : Prop :=
  ∀ (U : Over S) (p : GroupoidsOver.slice U ⟶ X) (u : U.left),
    Groupoids.Hom.Smooth p → Points.mapSlice p u = x → P U.left u

/-- `forallSmoothAt P X x` is the statement that every smooth scheme chart
through `x` has property `P` at the source point. -/
theorem forallSmoothAt_def {S : Scheme.{u}} (P : GermProperty.{u})
    (X : GroupoidsOver S) [AlgebraicStack X] (x : Points X) :
    forallSmoothAt P X x ↔
      ∀ (U : Over S) (p : GroupoidsOver.slice U ⟶ X) (u : U.left),
        Groupoids.Hom.Smooth p → Points.mapSlice p u = x → P U.left u :=
  Iff.rfl

namespace forallSmoothAt

/-- The universal smooth-scheme-through-`x` condition witnesses
`forallSmoothAt P X x`. -/
theorem of {S : Scheme.{u}} {P : GermProperty.{u}} {X : GroupoidsOver S}
    [AlgebraicStack X] {x : Points X}
    (h : ∀ (U : Over S) (p : GroupoidsOver.slice U ⟶ X) (u : U.left),
      Groupoids.Hom.Smooth p → Points.mapSlice p u = x → P U.left u) :
    forallSmoothAt P X x :=
  h

/-- If `forallSmoothAt P X x`, then every smooth morphism from a scheme through
`x` has `P` at the source point. -/
theorem apply {S : Scheme.{u}} {P : GermProperty.{u}} {X : GroupoidsOver S}
    [AlgebraicStack X] {x : Points X} (h : forallSmoothAt P X x) {U : Over S}
    (p : GroupoidsOver.slice U ⟶ X) (u : U.left) (hp : Groupoids.Hom.Smooth p)
    (hx : Points.mapSlice p u = x) : P U.left u :=
  h U p u hp hx

end forallSmoothAt

/-- There exists an algebraic space `U` over `S` and a smooth morphism
`p : U.toGroupoids ⟶ X` together with a point `u` of `|U|` such that
`Points.mapSpace p u = x` and `U` has property `P` at `u`. -/
def existsSmoothSpaceAt {S : Scheme.{u}} (P : GermProperty.{u})
    (X : GroupoidsOver S) [AlgebraicStack X] (x : Points X) : Prop :=
  ∃ (U : AlgebraicSpace S) (p : U.toGroupoids ⟶ X) (u : AlgebraicSpace.Points U),
    Groupoids.Hom.Smooth p ∧ Points.mapSpace p u = x ∧
      AlgebraicSpace.existsEtaleAt P U u

/-- `existsSmoothSpaceAt P X x` is the existence of a smooth algebraic-space
chart through `x` on which `U` has property `P` at `u`. -/
theorem existsSmoothSpaceAt_def {S : Scheme.{u}} (P : GermProperty.{u})
    (X : GroupoidsOver S) [AlgebraicStack X] (x : Points X) :
    existsSmoothSpaceAt P X x ↔
      ∃ (U : AlgebraicSpace S) (p : U.toGroupoids ⟶ X)
        (u : AlgebraicSpace.Points U),
        Groupoids.Hom.Smooth p ∧ Points.mapSpace p u = x ∧
          AlgebraicSpace.existsEtaleAt P U u :=
  Iff.rfl

namespace existsSmoothSpaceAt

/-- A smooth morphism from an algebraic space through `x` on which `U` has
property `P` at `u` witnesses `existsSmoothSpaceAt P X x`. -/
theorem of {S : Scheme.{u}} {P : GermProperty.{u}} {X : GroupoidsOver S}
    [AlgebraicStack X] {x : Points X} {U : AlgebraicSpace S}
    (p : U.toGroupoids ⟶ X) (u : AlgebraicSpace.Points U)
    [Groupoids.Hom.Smooth p] (hx : Points.mapSpace p u = x)
    (hP : AlgebraicSpace.existsEtaleAt P U u) :
    existsSmoothSpaceAt P X x :=
  ⟨U, p, u, inferInstance, hx, hP⟩

/-- An algebraic stack satisfying `existsSmoothSpaceAt P X x` admits a smooth
algebraic-space chart through `x` on which the source has property `P` at `u`. -/
theorem spec {S : Scheme.{u}} {P : GermProperty.{u}} {X : GroupoidsOver S}
    [AlgebraicStack X] {x : Points X} (h : existsSmoothSpaceAt P X x) :
    ∃ (U : AlgebraicSpace S) (p : U.toGroupoids ⟶ X)
      (u : AlgebraicSpace.Points U),
      Groupoids.Hom.Smooth p ∧ Points.mapSpace p u = x ∧
        AlgebraicSpace.existsEtaleAt P U u :=
  h

end existsSmoothSpaceAt

/-- Every smooth morphism `p : U.toGroupoids ⟶ X` from an algebraic space over
`S` and every point `u` of `|U|` with `Points.mapSpace p u = x` has the
property that `U` has `P` at `u`. -/
def forallSmoothSpaceAt {S : Scheme.{u}} (P : GermProperty.{u})
    (X : GroupoidsOver S) [AlgebraicStack X] (x : Points X) : Prop :=
  ∀ (U : AlgebraicSpace S) (p : U.toGroupoids ⟶ X) (u : AlgebraicSpace.Points U),
    Groupoids.Hom.Smooth p → Points.mapSpace p u = x →
      AlgebraicSpace.existsEtaleAt P U u

/-- `forallSmoothSpaceAt P X x` is the statement that every smooth
algebraic-space chart through `x` has property `P` at the source point. -/
theorem forallSmoothSpaceAt_def {S : Scheme.{u}} (P : GermProperty.{u})
    (X : GroupoidsOver S) [AlgebraicStack X] (x : Points X) :
    forallSmoothSpaceAt P X x ↔
      ∀ (U : AlgebraicSpace S) (p : U.toGroupoids ⟶ X)
        (u : AlgebraicSpace.Points U),
        Groupoids.Hom.Smooth p → Points.mapSpace p u = x →
          AlgebraicSpace.existsEtaleAt P U u :=
  Iff.rfl

namespace forallSmoothSpaceAt

/-- The universal smooth algebraic-space-through-`x` condition witnesses
`forallSmoothSpaceAt P X x`. -/
theorem of {S : Scheme.{u}} {P : GermProperty.{u}} {X : GroupoidsOver S}
    [AlgebraicStack X] {x : Points X}
    (h : ∀ (U : AlgebraicSpace S) (p : U.toGroupoids ⟶ X)
      (u : AlgebraicSpace.Points U),
      Groupoids.Hom.Smooth p → Points.mapSpace p u = x →
        AlgebraicSpace.existsEtaleAt P U u) :
    forallSmoothSpaceAt P X x :=
  h

/-- If `forallSmoothSpaceAt P X x`, then every smooth morphism from an algebraic
space through `x` has property `P` at the source point. -/
theorem apply {S : Scheme.{u}} {P : GermProperty.{u}} {X : GroupoidsOver S}
    [AlgebraicStack X] {x : Points X} (h : forallSmoothSpaceAt P X x)
    {U : AlgebraicSpace S} (p : U.toGroupoids ⟶ X) (u : AlgebraicSpace.Points U)
    (hp : Groupoids.Hom.Smooth p) (hx : Points.mapSpace p u = x) :
    AlgebraicSpace.existsEtaleAt P U u :=
  h U p u hp hx

end forallSmoothSpaceAt


/-- Let `P` be a smooth-local property of scheme germs, let `X`
be an algebraic stack, and let `x` be a point of `X`. Then `P` holds at every
smooth scheme chart through `x` if and only if it holds at some smooth scheme
chart through `x`. -/
@[stacks 04YI]
theorem forallSmoothAt_iff_existsSmoothAt {S : Scheme.{u}}
    (P : GermProperty.{u}) (hP : P.IsSmoothLocal)
    (X : GroupoidsOver S) [AlgebraicStack X] (x : Points X) :
    forallSmoothAt P X x ↔ existsSmoothAt P X x :=
  sorry

/-- Let `P` be a smooth-local property of scheme germs, let `X`
be an algebraic stack, and let `x` be a point of `X`. There exists a smooth
scheme chart through `x` with property `P` if and only if there exists a smooth
algebraic-space chart through `x` on which the source has property `P`. -/
@[stacks 04YI]
theorem existsSmoothAt_iff_existsSmoothSpaceAt {S : Scheme.{u}}
    (P : GermProperty.{u}) (hP : P.IsSmoothLocal)
    (X : GroupoidsOver S) [AlgebraicStack X] (x : Points X) :
    existsSmoothAt P X x ↔ existsSmoothSpaceAt P X x :=
  sorry

/-- Let `P` be a smooth-local property of scheme germs, let `X`
be an algebraic stack, and let `x` be a point of `X`. There exists a smooth
algebraic-space chart through `x` on which the source has property `P` if and
only if every smooth algebraic-space chart through `x` has property `P` on the
source. -/
@[stacks 04YI]
theorem existsSmoothSpaceAt_iff_forallSmoothSpaceAt {S : Scheme.{u}}
    (P : GermProperty.{u}) (hP : P.IsSmoothLocal)
    (X : GroupoidsOver S) [AlgebraicStack X] (x : Points X) :
    existsSmoothSpaceAt P X x ↔ forallSmoothSpaceAt P X x :=
  sorry

/-- If `X` is a scheme `U` over `S` and `u` is a point of `U`,
then `existsSmoothAt P (GroupoidsOver.slice U) (Points.ofSlice u)` is equivalent
to `P U.left u`. -/
@[stacks 04YI]
theorem existsSmoothAt_slice {S : Scheme.{u}} (P : GermProperty.{u})
    (hP : P.IsSmoothLocal) (U : Over S) (u : U.left) :
    existsSmoothAt P (GroupoidsOver.slice U) (Points.ofSlice u) ↔ P U.left u :=
  sorry

/-- If `X` is an algebraic space `F` over `S` and `x` is a
point of `F`, then `existsSmoothAt P F.toGroupoids (Points.ofAlgebraicSpace x)`
is equivalent to `F` having property `P` at `x`. -/
@[stacks 04YI]
theorem existsSmoothAt_toGroupoids {S : Scheme.{u}} (P : GermProperty.{u})
    (hP : P.IsSmoothLocal) (F : AlgebraicSpace S) (x : AlgebraicSpace.Points F) :
    existsSmoothAt P F.toGroupoids (Points.ofAlgebraicSpace x) ↔
      AlgebraicSpace.hasEtaleLocalAt P hP.isEtaleLocal F x :=
  sorry

/-- If `U` is a scheme over `S` and `u` is a point of `U`, then every smooth
scheme chart of `GroupoidsOver.slice U` through `ofSlice u` has property `P` if
and only if `P` holds at `(U.left, u)`. -/
theorem forallSmoothAt_slice {S : Scheme.{u}} (P : GermProperty.{u})
    (hP : P.IsSmoothLocal) (U : Over S) (u : U.left) :
    forallSmoothAt P (GroupoidsOver.slice U) (Points.ofSlice u) ↔ P U.left u :=
  sorry

/-- The smooth-local germ criterion at a point transports along an equivalence
to a scheme slice. -/
theorem existsSmoothAt_equivalence {S : Scheme.{u}} (P : GermProperty.{u})
    (hP : P.IsSmoothLocal) {X : GroupoidsOver S} [AlgebraicStack X] {U : Over S}
    (e : X ≌ GroupoidsOver.slice U) (x : Points X) :
    existsSmoothAt P X x ↔
      existsSmoothAt P (GroupoidsOver.slice U) (Points.map e.hom x) :=
  sorry

/-- An algebraic stack `X` has a smooth-local germ property `P` at a point `x`
when some smooth scheme chart through `x` has property `P`. -/
@[stacks 04YJ]
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
