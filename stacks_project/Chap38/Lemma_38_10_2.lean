/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import ReasLib.Algebra.Module.Devissage.CompleteAt.Flat
import StacksCheckRecall

@[expose] public section

open scoped DirectSum

universe u

/- Lemma 38.10.2 (1): a finite module admitting a complete dévissage at `q` and whose
localization at `q` is flat over the local base ring is finitely presented over `S`. -/
@[stacks 05I4] #check
  (Module.Devissage.CompleteAt.finitePresentation_of_flatAt :
    ∀ {R : Type u} [CommRing R] [IsLocalRing R]
      {S : FGAlgCat.{u} R} [Algebra.FinitePresentation R S.obj]
      {N : Type u} [AddCommGroup N] [Module S.obj N] [Module R N]
      [IsScalarTower R S.obj N] [Module.Finite S.obj N]
      {q : PrimeSpectrum S.obj}
      {hq : (IsLocalRing.closedPoint R).asIdeal =
        q.asIdeal.comap (algebraMap R S.obj)}
      (D : Module.Devissage.CompleteAt R S (FGModuleCat.of S.obj N)
        (IsLocalRing.closedPoint R) q hq)
      (hflat : Module.Flat R (LocalizedModule.AtPrime q.asIdeal N)),
      Module.FinitePresentation S.obj N)

/- Lemma 38.10.2 (2): a finite module admitting a complete dévissage at `q` and whose
localization at `q` is flat over the local base ring is free over that base ring. -/
@[stacks 05I4] #check
  (Module.Devissage.CompleteAt.free_of_flatAt :
    ∀ {R : Type u} [CommRing R] [IsLocalRing R]
      {S : FGAlgCat.{u} R} [Algebra.FinitePresentation R S.obj]
      {N : Type u} [AddCommGroup N] [Module S.obj N] [Module R N]
      [IsScalarTower R S.obj N] [Module.Finite S.obj N]
      {q : PrimeSpectrum S.obj}
      {hq : (IsLocalRing.closedPoint R).asIdeal =
        q.asIdeal.comap (algebraMap R S.obj)}
      (D : Module.Devissage.CompleteAt R S (FGModuleCat.of S.obj N)
        (IsLocalRing.closedPoint R) q hq)
      (hflat : Module.Flat R (LocalizedModule.AtPrime q.asIdeal N)),
      Module.Free R N)

/- Lemma 38.10.2 (3): a finite module admitting a complete dévissage at `q` and whose
localization at `q` is flat over the local base ring is, as an `R`-module, isomorphic to the
finite direct sum of the stage algebras with their dévissage multiplicities. -/
@[stacks 05I4] #check
  (Module.Devissage.CompleteAt.nonempty_linearEquiv_directSum_of_flatAt :
    ∀ {R : Type u} [CommRing R] [IsLocalRing R]
      {S : FGAlgCat.{u} R} [Algebra.FinitePresentation R S.obj]
      {N : Type u} [AddCommGroup N] [Module S.obj N] [Module R N]
      [IsScalarTower R S.obj N] [Module.Finite S.obj N]
      {q : PrimeSpectrum S.obj}
      {hq : (IsLocalRing.closedPoint R).asIdeal =
        q.asIdeal.comap (algebraMap R S.obj)}
      (D : Module.Devissage.CompleteAt R S (FGModuleCat.of S.obj N)
        (IsLocalRing.closedPoint R) q hq)
      (hflat : Module.Flat R (LocalizedModule.AtPrime q.asIdeal N)),
      Nonempty
        (N ≃ₗ[R]
          ⨁ i : Fin (D.toComplete.last + 1),
            (Fin (D.toComplete.stage i).rank → (D.toComplete.stage i).B)))
