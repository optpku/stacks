module

import StacksCheckRecall
public import ReasLib.AlgebraicGeometry.Scheme.ClosedAlgebraization

open AlgebraicGeometry AlgebraicGeometry.Scheme CategoryTheory CategoryTheory.Limits

universe u

/- Lemma 30.28.1: A cartesian adic ladder with closed first stage proper over the
quotient base algebraizes to a closed subscheme proper over the complete base. -/
@[stacks 0899] #check (AlgebraicGeometry.Scheme.exists_algebraizingClosedImmersion :
    ∀ {A : Type u} [CommRing A] [IsNoetherianRing A] (I : Ideal A) [IsAdicComplete I A]
    {X : Scheme.{u}} (f : X ⟶ Spec (CommRingCat.of A)) [IsSeparated f] [LocallyOfFiniteType f] [QuasiCompact f]
    (Z : ℕ+ → Scheme.{u}) (succ : ∀ n, Z n ⟶ Z (n + 1))
    (toStage : ∀ n, Z n ⟶ AdicThickening.stage f I n)
    (_ : ∀ n, IsPullback (succ n) (toStage n) (toStage (n + 1))
      (AdicThickening.transition f I n))
    [IsClosedImmersion (toStage 1)]
    [IsProper (toStage 1 ≫ AdicThickening.toSpec f I 1)],
    ∃ (W : Scheme.{u}) (ι : W ⟶ X) (π : ∀ n, Z n ⟶ W),
      IsClosedImmersion ι ∧ IsProper (ι ≫ f) ∧
        ∀ n, IsPullback (π n) (toStage n) ι (AdicThickening.ι f I n))
