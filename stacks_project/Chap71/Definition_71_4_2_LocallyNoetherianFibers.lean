/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import stacks_project.Chap71.Lemma_71_4_1_Fiber

/-!
# Locally Noetherian fibres of morphisms of algebraic spaces

The fibre of a morphism of algebraic spaces over a point of the target is
locally Noetherian when the equivalent conditions of Lemma 71.4.1 hold. The
fibres are locally Noetherian when this is true at every point of the target.
-/

@[expose] public section

open CategoryTheory AlgebraicGeometry

noncomputable section

universe u

namespace AlgebraicGeometry.AlgebraicSpace

/-- The fibre of a morphism `f : X ⟶ Y` of algebraic spaces over a point `y` of
`Points Y` is locally Noetherian when the equivalent conditions of
Lemma 71.4.1 hold. The defining field is existence of a field-valued
representative whose fibre is locally Noetherian. -/
@[mk_iff]
class IsLocallyNoetherianFiber {S : Scheme.{u}} {X Y : AlgebraicSpace S}
    (f : X ⟶ Y) (y : Points Y) : Prop where
  /-- Some field-valued representative of `y` has locally Noetherian fibre. -/
  existsField : LocallyNoetherianFiber.existsField f y

/-- The fibre of `f` over `y` is locally Noetherian if and only if the
equivalent conditions `existsEtale`, `forallEtale`, and `existsField` of
Lemma 71.4.1 hold. -/
theorem isLocallyNoetherianFiber_spec {S : Scheme.{u}} {X Y : AlgebraicSpace S}
    (f : X ⟶ Y) (y : Points Y) :
    IsLocallyNoetherianFiber f y ↔
      LocallyNoetherianFiber.existsEtale f y ∧
        LocallyNoetherianFiber.forallEtale f y ∧
          LocallyNoetherianFiber.existsField f y :=
  sorry

/-- The fibre of `f` over `y` is locally Noetherian if and only if some étale
scheme chart through `y` has locally Noetherian residue-field fibre. -/
theorem isLocallyNoetherianFiber_iff_existsEtale {S : Scheme.{u}}
    {X Y : AlgebraicSpace S} (f : X ⟶ Y) (y : Points Y) :
    IsLocallyNoetherianFiber f y ↔ LocallyNoetherianFiber.existsEtale f y :=
  sorry

/-- The fibre of `f` over `y` is locally Noetherian if and only if every étale
scheme chart through `y` has locally Noetherian residue-field fibre. -/
theorem isLocallyNoetherianFiber_iff_forallEtale {S : Scheme.{u}}
    {X Y : AlgebraicSpace S} (f : X ⟶ Y) (y : Points Y) :
    IsLocallyNoetherianFiber f y ↔ LocallyNoetherianFiber.forallEtale f y :=
  sorry

/-- The fibre of `f` over `y` is locally Noetherian if and only if some
field-valued representative of `y` has locally Noetherian fibre. -/
theorem isLocallyNoetherianFiber_iff_existsField {S : Scheme.{u}}
    {X Y : AlgebraicSpace S} (f : X ⟶ Y) (y : Points Y) :
    IsLocallyNoetherianFiber f y ↔ LocallyNoetherianFiber.existsField f y :=
  sorry

namespace IsLocallyNoetherianFiber

/-- A field-valued representative with locally Noetherian fibre witnesses that
the fibre of `f` over `y` is locally Noetherian. -/
theorem of {S : Scheme.{u}} {X Y : AlgebraicSpace S} {f : X ⟶ Y} {y : Points Y}
    (h : LocallyNoetherianFiber.existsField f y) :
    IsLocallyNoetherianFiber f y :=
  sorry

/-- If the fibre of `f` over `y` is locally Noetherian, then some field-valued
representative of `y` has locally Noetherian fibre. -/
theorem spec {S : Scheme.{u}} {X Y : AlgebraicSpace S} (f : X ⟶ Y)
    (y : Points Y) [IsLocallyNoetherianFiber f y] :
    LocallyNoetherianFiber.existsField f y :=
  sorry

end IsLocallyNoetherianFiber

/-- A morphism `f : X ⟶ Y` of algebraic spaces has locally Noetherian fibres
when the fibre of `f` over every point of `Points Y` is locally Noetherian. -/
@[mk_iff]
class LocallyNoetherianFibers {S : Scheme.{u}} {X Y : AlgebraicSpace S}
    (f : X ⟶ Y) : Prop where
  /-- The fibre of `f` over every point of `Points Y` is locally Noetherian. -/
  fiber : ∀ y : Points Y, IsLocallyNoetherianFiber f y

/-- The fibres of `f` are locally Noetherian if and only if, for every point of
`Points Y`, the equivalent conditions `existsEtale`, `forallEtale`, and
`existsField` of Lemma 71.4.1 hold. -/
theorem locallyNoetherianFibers_spec {S : Scheme.{u}} {X Y : AlgebraicSpace S}
    (f : X ⟶ Y) :
    LocallyNoetherianFibers f ↔
      (∀ y : Points Y, LocallyNoetherianFiber.existsEtale f y) ∧
        (∀ y : Points Y, LocallyNoetherianFiber.forallEtale f y) ∧
          (∀ y : Points Y, LocallyNoetherianFiber.existsField f y) :=
  sorry

/-- If the fibres of `f` are locally Noetherian, then the fibre over any point
of the target is locally Noetherian. -/
instance IsLocallyNoetherianFiber.ofFibers {S : Scheme.{u}}
    {X Y : AlgebraicSpace S} {f : X ⟶ Y} [h : LocallyNoetherianFibers f]
    {y : Points Y} : IsLocallyNoetherianFiber f y :=
  h.fiber y

namespace LocallyNoetherianFibers

/-- The identity morphism of an algebraic space has locally Noetherian fibres. -/
instance id {S : Scheme.{u}} {X : AlgebraicSpace S} :
    LocallyNoetherianFibers (𝟙 X) :=
  sorry

end LocallyNoetherianFibers

end AlgebraicGeometry.AlgebraicSpace
