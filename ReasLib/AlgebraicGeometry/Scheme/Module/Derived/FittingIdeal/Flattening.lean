/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import ReasLib.Algebra.Category.ModuleCat.Sheaf.FiniteLocallyFree.Rank
public import ReasLib.AlgebraicGeometry.RingedSpace.Module.Derived.Cohomology.Basic
public import ReasLib.AlgebraicGeometry.RingedSpace.Module.Derived.Perfect
public import ReasLib.AlgebraicGeometry.RingedSpace.Module.Derived.Pullback
public import ReasLib.AlgebraicGeometry.RingedSpace.Module.Derived.TorDimension
public import ReasLib.AlgebraicGeometry.RingedSpace.Module.OpenSubspace.Derived
public import ReasLib.AlgebraicGeometry.Scheme.Blowup.Basic
public import ReasLib.AlgebraicGeometry.Scheme.ClosedSubscheme.Closure

@[expose] public section

open AlgebraicGeometry CategoryTheory

noncomputable section

universe u

namespace AlgebraicGeometry.Scheme.ModuleDerived

/-- A perfect derived module whose cohomology sheaves have prescribed constant finite-local
ranks on a scheme-theoretically dense open admits an admissible blowup after which every
cohomology sheaf of its derived pullback is perfect and has Tor dimension at most one. -/
theorem exists_isAdmissibleBlowup_cohomology {X : Scheme.{u}}
    (E : RingedSpace.ModuleDerived X.toRingedSpace)
    (hE : RingedSpace.ModuleDerived.IsPerfect E) (U : X.Opens)
    (hU : schemeTheoreticallyDense U) (r : ℤ → ℕ)
    (h_rank : ∀ i : ℤ,
      SheafOfModules.IsFiniteLocallyFreeOfRank (r i)
        (RingedSpace.ModuleDerived.cohomologySheaf
          ((RingedSpace.moduleRestrictionToOpenDerived X.toRingedSpace U).obj E) i)) :
    ∃ (X' : Scheme.{u}) (b : X' ⟶ X),
      IsAdmissibleBlowup U b ∧
        ∀ i : ℤ,
          SheafOfModules.IsPerfect
              (RingedSpace.ModuleDerived.cohomologySheaf
                ((RingedSpace.modulePullbackDerived b.toShHom).obj E) i) ∧
            RingedSpace.ModuleHasTorDimensionLE
              (RingedSpace.ModuleDerived.cohomologySheaf
                ((RingedSpace.modulePullbackDerived b.toShHom).obj E) i) 1 := sorry

/-- On an integral scheme, a perfect derived module is degreewise finite locally free of
constant rank on a nonempty open and admits an admissible blowup along that open whose
derived pullback has perfect cohomology of Tor dimension at most one. -/
theorem exists_open_isAdmissibleBlowup_cohomology {X : Scheme.{u}} [IsIntegral X]
    (E : RingedSpace.ModuleDerived X.toRingedSpace)
    (hE : RingedSpace.ModuleDerived.IsPerfect E) :
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
                      ((RingedSpace.modulePullbackDerived b.toShHom).obj E) i) 1 := sorry

end AlgebraicGeometry.Scheme.ModuleDerived
