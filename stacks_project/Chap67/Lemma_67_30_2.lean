module

public import stacks_project.Chap67.Lemma_67_30_5_Flat

/-!
# Flatness of morphisms of algebraic spaces is a pointwise condition

A morphism of algebraic spaces is flat if and only if it is flat at every
point of the source.
-/

@[expose] public section

open CategoryTheory AlgebraicGeometry

universe u

namespace AlgebraicGeometry.AlgebraicSpace

/-- Lemma 67.30.2: Let `S` be a scheme. Let `f : X ⟶ Y` be a morphism of
algebraic spaces over `S`. Then `f` is flat if and only if `f` is flat at
all points of `|X|` (`Points X`). -/
@[stacks 08EW]
theorem flat_iff_forall_flatAt {S : Scheme.{u}} {X Y : AlgebraicSpace S}
    (f : X ⟶ Y) : Flat f ↔ ∀ x : Points X, FlatAt f x :=
  sorry

/-- A flat morphism of algebraic spaces is flat at every point of its source. -/
theorem flatAt_of_flat {S : Scheme.{u}} {X Y : AlgebraicSpace S}
    (f : X ⟶ Y) [Flat f] (x : Points X) : FlatAt f x :=
  sorry

/-- A morphism of algebraic spaces that is flat at every point of its source
is flat. -/
theorem Flat.of_forall_flatAt {S : Scheme.{u}} {X Y : AlgebraicSpace S}
    (f : X ⟶ Y) (h : ∀ x : Points X, FlatAt f x) : Flat f :=
  sorry

end AlgebraicGeometry.AlgebraicSpace
