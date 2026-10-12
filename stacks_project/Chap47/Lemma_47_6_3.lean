/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import ReasLib.Algebra.Module.MatlisDuality.FinitelyGenerated
import StacksCheckRecall

@[expose] public section

noncomputable section

universe u

open CategoryTheory

/- Lemma 47.6.3 (1): Dualization into an injective hull of the residue field is exact on
finitely generated modules over an Artinian local ring. -/
@[stacks 08YZ] #check
  (LinearMap.IsInjectiveHull.dualFunctor_exact :
    ∀ (R E : Type u) [CommRing R] [IsLocalRing R] [IsArtinianRing R]
      [AddCommGroup E] [Module R E] [Module.Injective R E]
      (ι : IsLocalRing.ResidueField R →ₗ[R] E) (hι : ι.IsInjectiveHull),
      exactFunctor (FGModuleCat.{u} R)ᵒᵖ (FGModuleCat.{u} R)
        (LinearMap.IsInjectiveHull.dualFunctor R E ι hι))

/- Lemma 47.6.3 (2): Dualization into an injective hull of the residue field is an
anti-equivalence on finitely generated modules over an Artinian local ring. -/
@[stacks 08YZ] #check
  (LinearMap.IsInjectiveHull.dualFunctorIsEquivalence :
    ∀ (R E : Type u) [CommRing R] [IsLocalRing R] [IsArtinianRing R]
      [AddCommGroup E] [Module R E] [Module.Injective R E]
      (ι : IsLocalRing.ResidueField R →ₗ[R] E) (hι : ι.IsInjectiveHull),
      Functor.IsEquivalence (LinearMap.IsInjectiveHull.dualFunctor R E ι hι))

/- Lemma 47.6.3 (3): Canonical evaluation identifies every finitely generated module with
its double dual into an injective hull of the residue field. -/
@[stacks 08YZ] #check
  (LinearMap.IsInjectiveHull.evaluationIsIso :
    ∀ (R E : Type u) [CommRing R] [IsLocalRing R] [IsArtinianRing R]
      [AddCommGroup E] [Module R E] [Module.Injective R E]
      (ι : IsLocalRing.ResidueField R →ₗ[R] E) (hι : ι.IsInjectiveHull),
      IsIso (LinearMap.IsInjectiveHull.evaluation R E ι hι))
