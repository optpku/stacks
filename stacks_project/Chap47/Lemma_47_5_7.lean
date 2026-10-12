/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import ReasLib.Algebra.Module.Injective.Prime
import StacksCheckRecall

@[expose] public section

universe u v

/- Lemma 47.5.7 (1): An injective hull of `R ⧸ p`, for a prime ideal `p`, is
indecomposable. -/
@[stacks 08Y8] #check (LinearMap.IsInjectiveHull.indecomposable_of_quotient :
  ∀ {R : Type u} [CommRing R] (p : Ideal R) [p.IsPrime]
    {E : Type v} [AddCommGroup E] [Module R E] [Module.Injective R E]
    (i : R ⧸ p →ₗ[R] E), i.IsInjectiveHull →
      CategoryTheory.Indecomposable (ModuleCat.of R E))

/- Lemma 47.5.7 (2): An injective hull of `R ⧸ p` extends along the canonical
embedding into `p.ResidueField` to an injective hull of `p.ResidueField`. -/
@[stacks 08Y8] #check (LinearMap.IsInjectiveHull.exists_residueField :
  ∀ {R : Type u} [CommRing R] (p : Ideal R) [p.IsPrime]
    {E : Type v} [AddCommGroup E] [Module R E] [Module.Injective R E]
    (i : R ⧸ p →ₗ[R] E), i.IsInjectiveHull →
      ∃ j : p.ResidueField →ₗ[R] E,
        j.comp ((Algebra.linearMap (R ⧸ p) p.ResidueField).restrictScalars R) = i ∧
          j.IsInjectiveHull)

/- Lemma 47.5.7 (3): After identifying `E` with its localization at `p`, it is
an injective hull of `p.ResidueField` over `Localization.AtPrime p`, compatibly
with the original hull embedding. -/
@[stacks 08Y8] #check (LinearMap.IsInjectiveHull.exists_residueField_atPrime :
  ∀ {R : Type u} [CommRing R] (p : Ideal R) [p.IsPrime]
    {E : Type v} [AddCommGroup E] [Module R E] [Module.Injective R E]
    (i : R ⧸ p →ₗ[R] E), i.IsInjectiveHull →
      ∃ (e : E ≃ₗ[R] LocalizedModule.AtPrime p E)
          (hL : Module.Injective (Localization.AtPrime p)
            (LocalizedModule.AtPrime p E))
          (j : p.ResidueField →ₗ[Localization.AtPrime p]
            LocalizedModule.AtPrime p E),
        e.toLinearMap = LocalizedModule.mkLinearMap p.primeCompl E ∧
          (j.restrictScalars R).comp
              ((Algebra.linearMap (R ⧸ p) p.ResidueField).restrictScalars R) =
            (LocalizedModule.mkLinearMap p.primeCompl E).comp i ∧
          @LinearMap.IsInjectiveHull (Localization.AtPrime p) _ p.ResidueField _ _
            (LocalizedModule.AtPrime p E) _ _ hL j)
