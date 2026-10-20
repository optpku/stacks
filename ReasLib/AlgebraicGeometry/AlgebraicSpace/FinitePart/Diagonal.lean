module

public import ReasLib.AlgebraicGeometry.AlgebraicSpace.FinitePart.Basic

/-! # Diagonals of the finite-part presheaf

The relative diagonal of the finite-part presheaf is a representable open immersion,
and its absolute diagonal is representable by schemes.
-/

@[expose] public section

open CategoryTheory AlgebraicGeometry Limits MorphismProperty

universe u

namespace AlgebraicGeometry.AlgebraicSpace.FinitePart

/-- The relative diagonal of the finite-part presheaf over its target is a
representable open immersion. -/
theorem isOpenImmersion_diagonal {S : Scheme.{u}} {X Y : AlgebraicSpace S}
    (f : X ⟶ Y) :
    (over (@AlgebraicGeometry.IsOpenImmersion : MorphismProperty Scheme.{u})).presheaf
      (diagonal f) := by
  sorry

/-- The relative diagonal of the finite-part presheaf is representable by schemes. -/
theorem relativelyRepresentable_diagonal {S : Scheme.{u}} {X Y : AlgebraicSpace S}
    (f : X ⟶ Y) : yoneda.relativelyRepresentable (diagonal f) :=
  (isOpenImmersion_diagonal f).rep

/-- The absolute diagonal of the finite-part presheaf is representable by schemes. -/
theorem relativelyRepresentable_diag {S : Scheme.{u}} {X Y : AlgebraicSpace S}
    (f : X ⟶ Y) : yoneda.relativelyRepresentable (diag f) := by
  sorry

/-- For a morphism of algebraic spaces, the finite-part presheaf has a representable
open relative diagonal and a representable absolute diagonal. -/
theorem diagonals {S : Scheme.{u}} {X Y : AlgebraicSpace S} (f : X ⟶ Y) :
    (over (@AlgebraicGeometry.IsOpenImmersion : MorphismProperty Scheme.{u})).presheaf
      (diagonal f) ∧ yoneda.relativelyRepresentable (diag f) :=
  ⟨isOpenImmersion_diagonal f, relativelyRepresentable_diag f⟩

end AlgebraicGeometry.AlgebraicSpace.FinitePart
