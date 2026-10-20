module

public import stacks_project.Chap101.Definition_101_38_1_SchemeTheoreticImage
public import ReasLib.AlgebraicGeometry.AlgebraicStack.SchemeTheoreticImage.Existence

/-!
# Existence of scheme-theoretic images of morphisms of algebraic stacks

`IsSchemeTheoreticImage` is owned by Definition 101.38.1. This module records
when a morphism factors through a closed substack and when a scheme-theoretic
image exists; there is no chosen image carrier.
-/

@[expose] public section

open CategoryTheory AlgebraicGeometry
open scoped Bicategory

universe u

namespace AlgebraicGeometry.AlgebraicStack

/-- A morphism `f : X ⟶ Y` of algebraic stacks factors through a closed
substack `Z` of `Y` if there is a 1-morphism `toZ : X ⟶ Z.Y` with
`toZ ≫ Z.ι = f`. -/
def factorsThrough {S : Scheme.{u}} {X Y : GroupoidsOver S}
    [AlgebraicStack X] [AlgebraicStack Y] (f : X ⟶ Y) (Z : ClosedSubstack Y) :
    Prop :=
  ∃ toZ : X ⟶ Z.Y, toZ ≫ Z.ι = f

namespace factorsThrough

/-- Package a 1-morphism into a closed substack whose composite with the
inclusion recovers `f`. -/
theorem mk {S : Scheme.{u}} {X Y : GroupoidsOver S}
    [AlgebraicStack X] [AlgebraicStack Y] {f : X ⟶ Y} {Z : ClosedSubstack Y}
    (toZ : X ⟶ Z.Y) (hfac : toZ ≫ Z.ι = f) : factorsThrough f Z :=
  ⟨toZ, hfac⟩

/-- A factorization through a closed substack supplies a 1-morphism into the
substack whose composite with the inclusion is `f`. -/
theorem spec {S : Scheme.{u}} {X Y : GroupoidsOver S}
    [AlgebraicStack X] [AlgebraicStack Y] {f : X ⟶ Y} {Z : ClosedSubstack Y}
    (h : factorsThrough f Z) : ∃ toZ : X ⟶ Z.Y, toZ ≫ Z.ι = f :=
  h

/-- Factoring through a closed substack is the existence of a 1-morphism into
the substack whose composite with the inclusion is `f`. -/
theorem iff {S : Scheme.{u}} {X Y : GroupoidsOver S}
    [AlgebraicStack X] [AlgebraicStack Y] (f : X ⟶ Y) (Z : ClosedSubstack Y) :
    factorsThrough f Z ↔ ∃ toZ : X ⟶ Z.Y, toZ ≫ Z.ι = f :=
  Iff.rfl

end factorsThrough

#check (AlgebraicGeometry.AlgebraicStack.HasSchemeTheoreticImage :
  ∀ {S : Scheme.{u}} {X Y : GroupoidsOver S}
    [AlgebraicStack X] [AlgebraicStack Y], (X ⟶ Y) → Prop)

/-- Existence of a scheme-theoretic image is the existence of a closed-substack
factorization that is a scheme-theoretic image. -/
theorem hasSchemeTheoreticImage_iff {S : Scheme.{u}} {X Y : GroupoidsOver S}
    [AlgebraicStack X] [AlgebraicStack Y] (f : X ⟶ Y) :
    HasSchemeTheoreticImage f ↔
      ∃ (Z : ClosedSubstack Y) (toImage : X ⟶ Z.Y),
        IsSchemeTheoreticImage f toImage Z.ι :=
  by
    constructor
    · rintro ⟨Z, toImage, ι, h⟩
      exact ⟨{ Y := Z.toGroupoids
               ι := ι
               isAlgebraicStack := inferInstance
               isClosedImmersion := h.isClosedImmersion
               isStrictlyFull := { full := h.full, faithful := h.faithful } },
        toImage, h⟩
    · rintro ⟨Z, toImage, h⟩
      exact ⟨AlgebraicStacks.of Z.Y, toImage, Z.ι, h⟩

end AlgebraicGeometry.AlgebraicStack
