module

public import stacks_project.Chap68.Lemma_68_5_3
import StacksCheckRecall

@[expose] public section

open CategoryTheory AlgebraicGeometry AlgebraicGeometry.AlgebraicSpace

universe u

variable {S : Scheme.{u}} {X Y : AlgebraicSpace S} (f : X ⟶ Y)
  (hf : yoneda.relativelyRepresentable f)

section

variable [IsDecent Y]

/- Lemma 68.6.5 (1): Let `S` be a scheme. Let `X`, `Y` be algebraic spaces over `S`.
Let `X ⟶ Y` be a representable morphism. If `Y` is decent, then so is `X`. -/
@[stacks 0ABT] #check (IsDecent.of_relativelyRepresentable f hf : IsDecent X)

end

section

variable [IsReasonable Y]

/- Lemma 68.6.5 (2): Let `S` be a scheme. Let `X`, `Y` be algebraic spaces over `S`.
Let `X ⟶ Y` be a representable morphism. If `Y` is reasonable, then so is `X`. -/
@[stacks 0ABT] #check (IsReasonable.of_relativelyRepresentable f hf : IsReasonable X)

end
