module

public import Mathlib.AlgebraicGeometry.OpenImmersion
public import Mathlib.CategoryTheory.MorphismProperty.Comma
public import Mathlib.CategoryTheory.MorphismProperty.Representable
public import stacks_project.Chap79.Lemma_79_12_7_Hom

/-!
# Representability of the diagonals of the finite-part functor
-/

@[expose] public section

open CategoryTheory AlgebraicGeometry AlgebraicSpace Limits MorphismProperty

noncomputable section

universe u

namespace AlgebraicGeometry.AlgebraicSpace.FinitePart

/-- Lemma 79.12.7 (1): Let `S` be a scheme. Let `f : X ⟶ Y` be a morphism of
algebraic spaces over `S`. The diagonal of `(X/Y)_fin ⟶ Y`,
`(X/Y)_fin ⟶ (X/Y)_fin ×_Y (X/Y)_fin`, is representable (by schemes) and an
open immersion. -/
@[stacks 04PK]
theorem isOpenImmersion_diagonal {S : Scheme.{u}} {X Y : AlgebraicSpace S}
    (f : X ⟶ Y) :
    (over (@AlgebraicGeometry.IsOpenImmersion : MorphismProperty Scheme.{u})).presheaf (diagonal f) :=
  sorry

/-- The relative diagonal of `(X/Y)_fin ⟶ Y` is representable by schemes. -/
theorem relativelyRepresentable_diagonal {S : Scheme.{u}} {X Y : AlgebraicSpace S}
    (f : X ⟶ Y) : yoneda.relativelyRepresentable (diagonal f) :=
  sorry

/-- Lemma 79.12.7 (2): Let `S` be a scheme. Let `f : X ⟶ Y` be a morphism of
algebraic spaces over `S`. The absolute diagonal
`(X/Y)_fin ⟶ (X/Y)_fin × (X/Y)_fin` is representable (by schemes). -/
@[stacks 04PK]
theorem relativelyRepresentable_diag {S : Scheme.{u}} {X Y : AlgebraicSpace S}
    (f : X ⟶ Y) : yoneda.relativelyRepresentable (diag f) :=
  sorry

end AlgebraicGeometry.AlgebraicSpace.FinitePart
