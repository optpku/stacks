/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.AlgebraicGeometry.AlgebraicSpace.ClosedSubspace.IntegralImage
import StacksCheckRecall

open CategoryTheory AlgebraicGeometry AlgebraicGeometry.AlgebraicSpace

universe u

/- Lemma 82.7.1. In Situation 82.2.1, for good algebraic spaces X and Y over B,
an integral closed subspace of X has a unique integral closed image in Y with a
dominant factorization. The statement holds more generally for any morphism
with decent target: the generic-point construction uses no base, finite-type,
or dimension hypotheses. For a proper morphism the factorization is proper
and surjective, as recorded by the following two companion checks. -/
@[stacks 0EEG] #check (AlgebraicGeometry.AlgebraicSpace.ClosedSubspace.existsUnique_integralImage :
  ∀ {S : Scheme.{u}}
    {X Y : AlgebraicSpace S} [IsDecent Y] (f : X ⟶ Y)
    (Z : ClosedSubspace X) [IsIntegral Z.X],
    ∃ Z' : ClosedSubspace Y,
      IsIntegral Z'.X ∧
        (∃ g : Z.X ⟶ Z'.X, g ≫ Z'.ι = Z.ι ≫ f ∧ Dominant g) ∧
          ∀ (W : ClosedSubspace Y),
            IsIntegral W.X →
              (∃ g : Z.X ⟶ W.X, g ≫ W.ι = Z.ι ≫ f ∧ Dominant g) →
                ∃! φ : W.X ⟶ Z'.X, φ ≫ Z'.ι = W.ι)

#check (AlgebraicGeometry.AlgebraicSpace.ClosedSubspace.proper_hom_integralImage :
  ∀ {S : Scheme.{u}} {X Y : AlgebraicSpace S}
    {f : X ⟶ Y} [Proper f] (Z : ClosedSubspace X) [IsIntegral Z.X]
    (Z' : ClosedSubspace Y) [IsIntegral Z'.X] (g : Z.X ⟶ Z'.X)
    (hg : g ≫ Z'.ι = Z.ι ≫ f) (h_dom : Dominant g),
    Proper g)

#check (AlgebraicGeometry.AlgebraicSpace.ClosedSubspace.surjective_hom_integralImage :
  ∀ {S : Scheme.{u}} {X Y : AlgebraicSpace S}
    {f : X ⟶ Y} [Proper f] (Z : ClosedSubspace X) [IsIntegral Z.X]
    (Z' : ClosedSubspace Y) [IsIntegral Z'.X] (g : Z.X ⟶ Z'.X)
    (hg : g ≫ Z'.ι = Z.ι ≫ f) (h_dom : Dominant g),
    Surjective g)
