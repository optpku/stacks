module

public import ReasLib.AlgebraicGeometry.AlgebraicSpace.Morphism.Unramified.Differentials
import StacksCheckRecall

/-!
# Unramified morphisms of algebraic spaces versus vanishing differentials

A morphism of algebraic spaces is unramified if and only if it is locally of
finite type and either its sheaf of relative differentials vanishes or it is
formally unramified.
-/

open CategoryTheory

universe u

/- Lemma 76.14.7 (1): a morphism of algebraic spaces over a scheme is unramified
if and only if it is locally of finite type and its relative differentials vanish. -/
@[stacks 04GA] #check
  (AlgebraicGeometry.AlgebraicSpace.unramified_iff_locallyOfFiniteType_and_isZero_relativeDifferentials :
    ∀ {S : AlgebraicGeometry.Scheme.{u}} {X Y : AlgebraicGeometry.AlgebraicSpace S}
      (f : X ⟶ Y),
      AlgebraicGeometry.AlgebraicSpace.Unramified f ↔
        AlgebraicGeometry.AlgebraicSpace.LocallyOfFiniteType f ∧
          CategoryTheory.Limits.IsZero
            (AlgebraicGeometry.AlgebraicSpace.Hom.relativeDifferentials f))

/- Lemma 76.14.7 (2): a morphism of algebraic spaces over a scheme is unramified
if and only if it is locally of finite type and formally unramified. -/
@[stacks 04GA] #check
  (AlgebraicGeometry.AlgebraicSpace.unramified_iff_locallyOfFiniteType_and_formallyUnramified :
    ∀ {S : AlgebraicGeometry.Scheme.{u}} {X Y : AlgebraicGeometry.AlgebraicSpace S}
      (f : X ⟶ Y),
      AlgebraicGeometry.AlgebraicSpace.Unramified f ↔
        AlgebraicGeometry.AlgebraicSpace.LocallyOfFiniteType f ∧
          AlgebraicGeometry.AlgebraicSpace.FormallyUnramified f)
