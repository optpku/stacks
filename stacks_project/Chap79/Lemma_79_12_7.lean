module

public import ReasLib.AlgebraicGeometry.AlgebraicSpace.FinitePart.Diagonal
import StacksCheckRecall

/-! # Diagonals of the finite-part presheaf -/

@[expose] public section

open CategoryTheory AlgebraicGeometry Limits MorphismProperty

universe u

/- Lemma 79.12.7: The finite-part presheaf of an arbitrary morphism of algebraic spaces
has a relative diagonal that is representable by schemes and an open immersion,
and an absolute diagonal that is representable by schemes. -/
@[stacks 04PK] #check (AlgebraicGeometry.AlgebraicSpace.FinitePart.diagonals :
  ∀ {S : Scheme.{u}} {X Y : AlgebraicSpace S} (f : X ⟶ Y),
    (over (@AlgebraicGeometry.IsOpenImmersion : MorphismProperty Scheme.{u})).presheaf
      (AlgebraicGeometry.AlgebraicSpace.FinitePart.diagonal f) ∧
    yoneda.relativelyRepresentable (AlgebraicGeometry.AlgebraicSpace.FinitePart.diag f))

