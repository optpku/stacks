module

public import ReasLib.AlgebraicGeometry.Scheme.Module.Derived.FittingIdeal.Flattening
import StacksCheckRecall

@[expose] public section

open AlgebraicGeometry CategoryTheory

noncomputable section

universe u

namespace AlgebraicGeometry.Scheme.ModuleDerived

/- Lemma 38.40.3: on an integral scheme, a perfect derived module restricts to one
nonempty open where all cohomology sheaves have degree-dependent constant finite-local
rank, and admits an admissible blowup on which all pulled-back cohomology sheaves are
perfect of Tor dimension at most one. -/
@[stacks 0ESR]
#check (AlgebraicGeometry.Scheme.ModuleDerived.exists_open_isAdmissibleBlowup_cohomology :
  ∀ {X : Scheme.{u}} [IsIntegral X]
    (E : RingedSpace.ModuleDerived X.toRingedSpace)
    (hE : RingedSpace.ModuleDerived.IsPerfect E),
    ∃ U : X.Opens, Nonempty U ∧
      ∃ r : ℤ → ℕ,
        (∀ i : ℤ,
          SheafOfModules.IsFiniteLocallyFreeOfRank (r i)
            (RingedSpace.ModuleDerived.cohomologySheaf
              ((RingedSpace.moduleRestrictionToOpenDerived X.toRingedSpace U).obj E) i)) ∧
          ∃ (X' : Scheme.{u}) (b : X' ⟶ X),
            IsAdmissibleBlowup U b ∧
              ∀ i : ℤ,
                SheafOfModules.IsPerfect
                    (RingedSpace.ModuleDerived.cohomologySheaf
                      ((RingedSpace.modulePullbackDerived b.toShHom).obj E) i) ∧
                  RingedSpace.ModuleHasTorDimensionLE
                    (RingedSpace.ModuleDerived.cohomologySheaf
                      ((RingedSpace.modulePullbackDerived b.toShHom).obj E) i) 1)

end AlgebraicGeometry.Scheme.ModuleDerived
