module

public import ReasLib.AlgebraicGeometry.AlgebraicSpace.Module.Quasicoherent.ClosedImmersion
import StacksCheckRecall

/-!
# Lemma 67.14.3

Exceptional inverse image for quasi-coherent modules along a closed immersion
of algebraic spaces.

@stack 04CL
-/

@[expose] public section

open CategoryTheory

universe u

/- Lemma 67.14.3: for a closed immersion of algebraic spaces, pushforward on
quasi-coherent modules admits an exceptional inverse image as a right adjoint. -/
@[stacks 04CL] #check
  (AlgebraicGeometry.AlgebraicSpace.QCoh.pushforward_isLeftAdjoint :
    ∀ {S : AlgebraicGeometry.Scheme.{u}} {X Z : AlgebraicGeometry.AlgebraicSpace S}
      (i : Z ⟶ X) [AlgebraicGeometry.AlgebraicSpace.IsClosedImmersion i],
      (AlgebraicGeometry.AlgebraicSpace.QCoh.pushforward i).IsLeftAdjoint)
