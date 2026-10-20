module

public import Mathlib.Order.WithBotTop
public import Mathlib.RingTheory.AdicCompletion.Basic
public import ReasLib.Algebra.Homology.DerivedCategory.Dualizing
public import ReasLib.RingTheory.CohenMacaulay.SerreCondition
public import ReasLib.RingTheory.Depth
public import stacks_project.Chap58.Lemma_58_19_2
public import stacks_project.Chap58.Lemma_58_21_6_Purity

public import ReasLib.AlgebraicGeometry.PuncturedSpectrum.FiniteEtalePurity
import StacksCheckRecall

@[expose] public section

open CategoryTheory
open AlgebraicGeometry
open AlgebraicGeometry.Scheme
open AlgebraicGeometry.PuncturedSpectrum
open IsLocalRing

noncomputable section

universe u

/- Lemma 58.24.1: in Situation 58.19.1, if `A` has a dualizing complex and is
`f`-adically complete, either `A_f` is `(S₂)` with every irreducible component of
`X` not contained in `X₀` of dimension at least `4` or the restricted primewise
depth-dimension inequality holds, and purity holds at every maximal localization
of `A_f`, then finite étale restriction from `U` to `U₀` is essentially surjective. -/
@[stacks 0EK9] #check
  (AlgebraicGeometry.PuncturedSpectrum.finiteEtaleBaseChange_essSurj_of_dualizing_complete_purity :
    ∀ {A : Type u} [CommRing A] [IsNoetherianRing A] [IsLocalRing A]
      (f : maximalIdeal A)
      [Fact (∃ K : DerivedCategory (ModuleCat.{u} A), K.IsDualizing)]
      [IsAdicComplete (principalIdeal (f : A)) A]
      [Fact (dualizingCompleteNeighborhoodAlternative f)]
      [Fact (hasPurityAtMaximalsAway f)],
      (Scheme.finiteEtaleBaseChange (principalQuotientMap f)).EssSurj)
