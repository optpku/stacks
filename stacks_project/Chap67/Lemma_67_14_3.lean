module

public import stacks_project.Chap67.Lemma_67_14_3_Shriek
import StacksCheckRecall

/-!
# Lemma 67.14.3

Exceptional inverse image for quasi-coherent modules along a closed immersion
of algebraic spaces.

@stack 04CL
-/

@[expose] public section

open CategoryTheory
open AlgebraicGeometry
open AlgebraicGeometry.AlgebraicSpace
open AlgebraicGeometry.AlgebraicSpace.QCoh

universe u

variable {S : Scheme.{u}} {X Z : AlgebraicSpace S} (i : Z ⟶ X)
  [AlgebraicSpace.IsClosedImmersion i]

/- Lemma 67.14.3: for a closed immersion of algebraic spaces, pushforward on
quasi-coherent modules admits an exceptional inverse image as a right adjoint. -/
@[stacks 04CL] #check
  (pushforwardShriekAdjunction i : pushforward i ⊣ shriek i)

#check (shriek i : QCoh X ⥤ QCoh Z)

#check pushforward_isLeftAdjoint
