module

import StacksCheckRecall
public import ReasLib.RingTheory.WeakDimension.One

/-!
@stack 092S
-/

@[expose] public section

universe u

/- Lemma 15.105.18 (092S): weak dimension at most one is equivalent to flatness of all ideals,
flatness of finitely generated ideals, flatness of submodules of flat modules, and the valuation
property for every prime localization. -/
@[stacks 092S "Lemma 15.105.18"]
#check fun (A : Type u) [CommRing A] ↦
  (HasWeakDimensionLE.one_tfae (R := A) :
    List.TFAE
      [ HasWeakDimensionLE A 1,
        ∀ I : Ideal A, Module.Flat A I,
        ∀ I : Ideal A, I.FG → Module.Flat A I,
        ∀ (M : ModuleCat.{u} A) [Module.Flat A M] (N : Submodule A M),
          Module.Flat A N,
        ∀ p : PrimeSpectrum A,
          ∃ (_ : IsDomain (Localization.AtPrime p.asIdeal)),
            ValuationRing (Localization.AtPrime p.asIdeal) ])

#check @Ideal.flat_of_fg_flat
#check @Ring.LocallyValuation
#check @Ring.LocallyValuation.iff_ideals_flat
#check @Ring.LocallyValuation.submodule_flat
#check @HasWeakDimensionLE.ideal_flat
#check @HasWeakDimensionLE.submodule_flat
#check @HasWeakDimensionLE.one_iff_fg_ideals_flat
#check @HasWeakDimensionLE.one_iff_locallyValuation
