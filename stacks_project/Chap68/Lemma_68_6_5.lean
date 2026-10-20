module

public import ReasLib.AlgebraicGeometry.AlgebraicSpace.RepresentableConditions
import StacksCheckRecall

@[expose] public section

open CategoryTheory AlgebraicGeometry AlgebraicGeometry.AlgebraicSpace

universe u

/- Lemma 68.6.5 (1): Let `S` be a scheme. Let `X`, `Y` be algebraic spaces over `S`.
Let `X ⟶ Y` be a representable morphism. If `Y` is decent, then so is `X`. -/
@[stacks 0ABT] #check
  (AlgebraicGeometry.AlgebraicSpace.IsDecent.of_relativelyRepresentable :
    ∀ {S : Scheme.{u}} {X Y : AlgebraicSpace S} (f : X ⟶ Y)
      (hf : yoneda.relativelyRepresentable f) [IsDecent Y], IsDecent X)

/- Lemma 68.6.5 (2): Let `S` be a scheme. Let `X`, `Y` be algebraic spaces over `S`.
Let `X ⟶ Y` be a representable morphism. If `Y` is reasonable, then so is `X`. -/
@[stacks 0ABT] #check
  (AlgebraicGeometry.AlgebraicSpace.IsReasonable.of_relativelyRepresentable :
    ∀ {S : Scheme.{u}} {X Y : AlgebraicSpace S} (f : X ⟶ Y)
      (hf : yoneda.relativelyRepresentable f) [IsReasonable Y], IsReasonable X)
