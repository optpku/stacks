module

public import ReasLib.AlgebraicGeometry.Scheme.GermProperty
public import stacks_project.Chap66.Lemma_66_7_4_EtaleLocal
public import stacks_project.Chap100.Lemma_100_7_4_Points

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

end AlgebraicGeometry.AlgebraicStack
