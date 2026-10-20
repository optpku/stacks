module

import StacksCheckRecall
public import ReasLib.AlgebraicGeometry.AlgebraicSpace.ClosedAlgebraization

open AlgebraicGeometry AlgebraicGeometry.AlgebraicSpace
open CategoryTheory CategoryTheory.Limits
open AlgebraicGeometry.AlgebraicSpace.SchemeRealization

universe u

/- Lemma 76.43.1: A cartesian adic ladder with closed first stage proper over the
quotient base algebraizes to a closed subspace proper over the complete base. -/
@[stacks 08BG] #check (AlgebraicGeometry.AlgebraicSpace.exists_algebraizingClosedImmersion :
    ∀ {A : Type u} [CommRing A] [IsNoetherianRing A] (I : Ideal A) [IsAdicComplete I A]
    {X : AlgebraicSpace (Spec (CommRingCat.of A))} [Separated (toBase X)]
    [FiniteType (toBase X)] (Z : ℕ+ → AlgebraicSpace (Spec (CommRingCat.of A)))
    (succ : ∀ n, Z n ⟶ Z (n + 1))
    (toStage : ∀ n, Z n ⟶ AdicThickening.stage X I n)
    (h_pb : ∀ n, IsPullback (succ n) (toStage n) (toStage (n + 1))
      (AdicThickening.transition X I n))
    [IsClosedImmersion (toStage 1)]
    [Proper (toStage 1 ≫ AdicThickening.toSpec X I 1)],
    ∃ (W : AlgebraicSpace (Spec (CommRingCat.of A))) (ι : W ⟶ X)
      (π : ∀ n, Z n ⟶ W),
      IsClosedImmersion ι ∧ Proper (ι ≫ toBase X) ∧
        ∀ n, IsPullback (π n) (toStage n) ι (AdicThickening.ι X I n))
