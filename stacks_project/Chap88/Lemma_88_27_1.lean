module

public import ReasLib.AlgebraicGeometry.AlgebraicSpace.CompletionAlong.BaseChange
import StacksCheckRecall

open CategoryTheory AlgebraicGeometry AlgebraicGeometry.AlgebraicSpace TopologicalSpace

universe u

/- Lemma 88.27.1: Completion commutes with base change along a morphism of
locally Noetherian algebraic spaces, via the canonical comparison. -/
@[stacks 0GDQ] #check
  (AlgebraicGeometry.AlgebraicSpace.completionAlong.instIsIso_baseChangeHom :
    ∀ {S : Scheme.{u}} {X X1 : AlgebraicSpace S}
      [IsLocallyNoetherian X] [IsLocallyNoetherian X1] (h : X1 ⟶ X)
      (T : Closeds (Points X)),
      IsIso (AlgebraicGeometry.AlgebraicSpace.completionAlong.baseChangeHom h T))
