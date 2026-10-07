module

import StacksCheckRecall
public import ReasLib.AlgebraicGeometry.Scheme.Module.Ample.Relative.Cancellation

open AlgebraicGeometry CategoryTheory
open scoped AlgebraicGeometry

universe u

/- Lemma 29.37.10: if a module is relatively ample over a composite morphism and the first
morphism is quasi-compact, then it is relatively ample over the first morphism. -/
@[stacks 0C4L] #check
  (AlgebraicGeometry.RelativelyAmple.of_comp :
    ∀ {X Y S : Scheme.{u}} {L : X.Modules} (f : X ⟶ Y) (g : Y ⟶ S) [QuasiCompact f],
      RelativelyAmple (f ≫ g) L → RelativelyAmple f L)
