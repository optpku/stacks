module

import StacksCheckRecall
public import ReasLib.AlgebraicGeometry.Scheme.Module.Derived.FittingIdeal.Flattening

@[expose] public section

open AlgebraicGeometry CategoryTheory

noncomputable section

universe u

namespace AlgebraicGeometry.Scheme.ModuleDerived

/- Lemma 38.40.2: a perfect derived module whose cohomology sheaves have constant finite-local
rank after restriction to a scheme-theoretically dense open admits an admissible blowup after
which every cohomology sheaf of its derived pullback is perfect and has Tor dimension at most
one. -/
@[stacks 0ESQ] #check
  (AlgebraicGeometry.Scheme.ModuleDerived.exists_isAdmissibleBlowup_cohomology :
    ∀ {X : Scheme.{u}}
      (E : RingedSpace.ModuleDerived X.toRingedSpace)
      (hE : RingedSpace.ModuleDerived.IsPerfect E) (U : X.Opens)
      (hU : schemeTheoreticallyDense U) (r : ℤ → ℕ)
      (h_rank : ∀ i : ℤ,
        SheafOfModules.IsFiniteLocallyFreeOfRank (r i)
          (RingedSpace.ModuleDerived.cohomologySheaf
            ((RingedSpace.moduleRestrictionToOpenDerived X.toRingedSpace U).obj E) i))
      (tensorOnBlowups : ∀ {X' : Scheme.{u}} (b : X' ⟶ X),
        IsAdmissibleBlowup U b →
          DerivedCategory.DerivedTensor.Right.Has
            (C := RingedSpace.Modules X'.toRingedSpace)),
      ∃ (X' : Scheme.{u}) (b : X' ⟶ X) (hb : IsAdmissibleBlowup U b),
        letI := tensorOnBlowups b hb
        ∀ i : ℤ,
          SheafOfModules.IsPerfect
              (RingedSpace.ModuleDerived.cohomologySheaf
                ((RingedSpace.modulePullbackDerived b.toShHom).obj E) i) ∧
            RingedSpace.ModuleHasTorDimensionLE
              (RingedSpace.ModuleDerived.cohomologySheaf
                ((RingedSpace.modulePullbackDerived b.toShHom).obj E) i) 1)

end AlgebraicGeometry.Scheme.ModuleDerived
