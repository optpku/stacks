module

public import ReasLib.AlgebraicGeometry.ProjectiveSpace.HyperplaneSection.Twist
public import ReasLib.AlgebraicGeometry.RingedSpace.Module.Cohomology
public import ReasLib.AlgebraicGeometry.RingedSpace.Module.Derived.Cohomology.Delta
public import ReasLib.AlgebraicGeometry.Scheme.Module.Cohomology.AffinePushforward

/-!
# Cohomology of twisted hyperplane-section sequences

This file applies the canonical global-cohomology delta functor to integral twists of a
hyperplane-section sequence and compares the pushforward terms with cohomology on the
hyperplane.
-/

@[expose] public section

open CategoryTheory
open CategoryTheory.CohomologicalDeltaFunctor
open scoped AlgebraicGeometry

noncomputable section

universe u

namespace AlgebraicGeometry

variable {k : Type u} [Field k] {n : ℕ}
variable (P : ProjectiveSpaceOver (Spec (CommRingCat.of k)) n)

/-- The cohomology of the restriction of the `d`th twist to a hyperplane section. -/
noncomputable abbrev hyperplaneSectionTwistedHyperplaneCohomology
    (ℱ : P.scheme.Modules) (s : P.tautologicalSheaf.sections) (d : ℤ) (q : ℕ) :
    AddCommGrpCat :=
  RingedSpace.moduleCohomology
    (hyperplaneSectionTwistedHyperplaneModule P ℱ s d) q

/-- The six-object cohomology window of a short exact twisted hyperplane-section complex. -/
noncomputable def hyperplaneSectionTwistedCohomologyWindow
    (ℱ : P.scheme.Modules) (s : P.tautologicalSheaf.sections) (d : ℤ)
    (hS : (hyperplaneSectionTwistedShortComplex P ℱ s d).ShortExact) (q : ℕ) :
    ComposableArrows (ModuleCat (RingedSpace.globalSectionsRing P.scheme.toRingedSpace)) 5 :=
  (RingedSpace.Module.Derived.GlobalSections.Delta.cohomology
    P.scheme.toRingedSpace).exactWindow hS q

/-- After forgetting the global-section module structure, the pushforward term in the
cohomology window is isomorphic to cohomology of the restricted twist on the hyperplane. -/
theorem hyperplaneSectionTwistedRestrictionPushforwardCohomology_isomorphic
    (ℱ : P.scheme.Modules) [ℱ.IsQuasicoherent]
    (s : P.tautologicalSheaf.sections)
    [ProjectiveSpaceHyperplane P (P.tautologicalZeroSchemeι s)] (d : ℤ) (q : ℕ) :
    IsIsomorphic
      ((forget₂ (ModuleCat (RingedSpace.globalSectionsRing P.scheme.toRingedSpace))
        AddCommGrpCat.{u}).obj
          ((((RingedSpace.Module.Derived.GlobalSections.Delta.cohomology
            P.scheme.toRingedSpace).F q).obj).obj
              (hyperplaneSectionTwistedRestrictionPushforward P ℱ s d)))
      (hyperplaneSectionTwistedHyperplaneCohomology P ℱ s d q) := sorry

/-- The canonical cohomology window attached to every integral twist of a short exact
hyperplane-section sequence is exact. -/
theorem hyperplaneSectionTwistedCohomologySequence_exact
    (ℱ : P.scheme.Modules) (s : P.tautologicalSheaf.sections) (d : ℤ)
    (hℱ : hyperplaneSectionShortExactFor P ℱ s) (q : ℕ) :
    (hyperplaneSectionTwistedCohomologyWindow P ℱ s d
      (hyperplaneSectionTwistedShortExactFor_of_hyperplaneSectionShortExact
        P ℱ s hℱ d) q).Exact := sorry

end AlgebraicGeometry
