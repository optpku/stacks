/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.AlgebraicGeometry.Scheme.CoherentFormalModule.Completion.LocalConditions
import StacksCheckRecall

@[expose] public section

open CategoryTheory CategoryTheory.Limits Opposite
open AlgebraicGeometry
open Set TopologicalSpace

noncomputable section

universe u

namespace AlgebraicGeometry.Scheme.CoherentFormalModules

/- 0EJB::statement_repair::1 — Lemma 52.20.6: in Situation 52.16.1, a coherent formal
module satisfies the `(2, 3)`-inequalities under the local duality, cohomological
dimension, completed-stalk local freeness, and alternative Serre/component-dimension
or primewise depth-plus-dimension hypotheses. The source's unbound element `f` is
made explicit with `I.radical = (Ideal.span {f}).radical`, so `V(f) = V(I)`. -/
@[stacks 0EJB] #check (AlgebraicGeometry.Scheme.CoherentFormalModules.satisfiesInequalities_of_local_conditions :
  ∀
    {A : Type u} [CommRing A] [IsNoetherianRing A] [IsLocalRing A]
    [MonoidalCategory (DerivedCategory (ModuleCat.{u} A))]
    (S : AffineAlgebraizationSetup A)
    (f : A)
    -- Source context: f is not introduced in the Stacks statement; Lemma lemma-equivalence-better applies it with I = (f), and the proof needs V(f) = V(I).
    (h_I_radical : S.I.radical = (Ideal.span ({f} : Set A)).radical)
    (H : MonoidalClosed (DerivedCategory (ModuleCat.{u} A)))
    (h_a : S.a = IsLocalRing.maximalIdeal A)
    (h_dualizing :
      ∃ K : DerivedCategory (ModuleCat.{u} A), K.IsDualizingComplex H)
    (hcd : Ideal.LocalCohomology.dimension S.I S.I.fg_of_isNoetherianRing = 1)
    (F : CoherentFormalModules S.U.toScheme
      ((Scheme.idealSheafDataOfIdealOnSpec S.I).comap S.U.ι))
    (h_finiteLocallyFree :
      ∀ y : S.Y, (hy : S.y y ∈ S.U) →
        ∀ g : completedLocalRing S (closedFiberOpenPoint S y hy),
          g ∈ completedIdeal S (closedFiberOpenPoint S y hy) →
            Module.FiniteLocallyFree (Localization.Away g)
              (LocalizedModule.Away g
                (completedStalk S F (closedFiberOpenPoint S y hy))))
    (h_alternative :
      (SerreConditionS (Localization.Away f) 2 ∧
        (∀ Z : irreducibleComponents S.X,
          ¬ ((Z : Set S.X) ⊆ Set.range S.y) →
            (4 : WithBot ℕ∞) ≤ topologicalKrullDim Z)) ∨
      (∀ p : PrimeSpectrum A,
        p ∉ PrimeSpectrum.zeroLocus ({f} : Set A) →
          PrimeSpectrum.zeroLocus (p.asIdeal : Set A) ∩
              PrimeSpectrum.zeroLocus ({f} : Set A) ≠
            {IsLocalRing.closedPoint A} →
            (3 : EInt) <
              ((WithTop.map Int.ofNat
                (moduleDepth (Localization.AtPrime p.asIdeal)
                  (LocalizedModule.AtPrime p.asIdeal A)) : WithTop ℤ) : EInt) +
                WithBot.map (WithTop.map Int.ofNat)
                  (ringKrullDim (A ⧸ p.asIdeal)))),
    SatisfiesInequalities S F 2 3)

end AlgebraicGeometry.Scheme.CoherentFormalModules
