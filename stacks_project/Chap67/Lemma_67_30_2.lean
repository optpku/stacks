module

public import ReasLib.AlgebraicGeometry.AlgebraicSpace.Flat
import StacksCheckRecall

/-!
# Flatness of morphisms of algebraic spaces is a pointwise condition

A morphism of algebraic spaces is flat if and only if it is flat at every
point of the source.
-/

@[expose] public section

open CategoryTheory AlgebraicGeometry

universe u

namespace AlgebraicGeometry.AlgebraicSpace

/- Lemma 67.30.2: Let `S` be a scheme. Let `f : X ⟶ Y` be a morphism of
algebraic spaces over `S`. Then `f` is flat if and only if `f` is flat at
all points of `|X|` (`Points X`). -/
@[stacks 08EW] #check (AlgebraicGeometry.AlgebraicSpace.flat_iff_forall_flatAt :
  ∀ {S : Scheme.{u}} {X Y : AlgebraicSpace S} (f : X ⟶ Y),
    Flat f ↔ ∀ x : Points X, FlatAt f x)

end AlgebraicGeometry.AlgebraicSpace
