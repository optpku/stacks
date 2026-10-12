/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import ReasLib.RingTheory.Algebra.FinitePresentation.FlatFiniteTypeDomain
public import ReasLib.Algebra.Module.FinitePresentation.FlatFiniteTypeDomain
import StacksCheckRecall

universe u v w

/- Proposition 38.13.10 (1): a flat finite-type algebra over a domain is finitely presented. -/
@[stacks 053G] #check (Algebra.FinitePresentation.ofFlatFiniteTypeDomain :
  ∀ {R : Type u} [CommRing R] [IsDomain R]
    {S : Type v} [CommRing S] [Algebra R S] [Algebra.FiniteType R S] [Module.Flat R S],
    Algebra.FinitePresentation R S)

/- Proposition 38.13.10 (2): a finite module over a finite-type algebra over a domain is finitely
presented when it is flat over the domain. -/
@[stacks 053G] #check (Module.FinitePresentation.ofFiniteFlatFiniteTypeDomain :
  ∀ (R : Type u) [CommRing R] [IsDomain R]
    {S : Type v} [CommRing S] [Algebra R S] [Algebra.FiniteType R S]
    {M : Type w} [AddCommMonoid M] [Module S M] [Module.Finite S M]
    [Module R M] [IsScalarTower R S M] [Module.Flat R M],
    Module.FinitePresentation S M)
