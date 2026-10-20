module

public import ReasLib.AlgebraicGeometry.AlgebraicSpace.Morphism.FormallyUnramified.Differentials
import StacksCheckRecall

/-!
# Formal unramifiedness and vanishing of relative differentials

A morphism of algebraic spaces is formally unramified if and only if its sheaf
of relative differentials vanishes.
-/

open CategoryTheory AlgebraicGeometry AlgebraicGeometry.AlgebraicSpace
open CategoryTheory.Limits

universe u

/- Lemma 76.14.6: Let `S` be a scheme. Let `f : X ⟶ Y` be a morphism of
algebraic spaces over `S`. Then `f` is formally unramified if and only if the
sheaf of relative differentials vanishes. -/
@[stacks 04G9] #check
  (AlgebraicGeometry.AlgebraicSpace.formallyUnramified_iff_isZero_relativeDifferentials :
    ∀ {S : Scheme.{u}} {X Y : AlgebraicSpace S} (f : X ⟶ Y),
      FormallyUnramified f ↔ IsZero (Hom.relativeDifferentials f))
