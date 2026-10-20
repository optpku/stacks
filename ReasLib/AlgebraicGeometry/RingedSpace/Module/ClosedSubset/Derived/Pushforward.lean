module

public import ReasLib.AlgebraicGeometry.RingedSpace.Module.ClosedSubset.Derived
import Mathlib.Tactic.CrossRefAttribute

/-!
# Derived sections with support of closed-subset pushforwards

This leaf records the degree-zero closed-subset objects used to compute derived sections with
support after exact pushforward.  The primary surface uses derived direct image; a companion
statement retains the underived-single presentation used in source-facing calculations.
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits TopologicalSpace

noncomputable section

universe u

namespace AlgebraicGeometry.RingedSpace.ClosedSubset.Derived.Pushforward

variable (X : RingedSpace.{u}) (Z : Closeds X)

/-- A closed-subset module regarded as a degree-zero derived object. -/
@[stacks 0A3B "degree-zero closed-subset derived module"]
abbrev single (M : RingedSpace.ClosedSubset.Modules X (Z : Set X)) :
    ModuleDerived X Z :=
  (DerivedCategory.singleFunctor
    (RingedSpace.ClosedSubset.Modules X (Z : Set X)) 0).obj M

/-- Derived sections with support of the derived direct image of a degree-zero closed-subset
module. -/
@[stacks 0A3B "derived sections with support of a closed-subset pushforward"]
abbrev localCohomology (M : RingedSpace.ClosedSubset.Modules X (Z : Set X)) :
    ModuleDerived X Z :=
  (SectionsWithSupport.derived X Z).obj ((Pushforward.derived X Z).obj (single X Z M))

/-- Positive homology vanishes for derived sections with support of a degree-zero closed-subset
pushforward. -/
@[stacks 0A3B "higher derived sections with support of a closed-subset pushforward"]
theorem higherHomology_isZero
    (M : RingedSpace.ClosedSubset.Modules X (Z : Set X)) (p : ℕ) :
    IsZero
      ((DerivedCategory.homologyFunctor
        (RingedSpace.ClosedSubset.Modules X (Z : Set X)) (p + 1)).obj
          (localCohomology X Z M)) := sorry

/-- Source-facing form using the degree-zero ambient object of the underived closed-subset
pushforward. -/
@[stacks 0A3B "higher derived sections with support of an underived pushforward"]
theorem underivedSingle_higherHomology_isZero
    (M : RingedSpace.ClosedSubset.Modules X (Z : Set X)) (p : ℕ) :
    IsZero
      ((DerivedCategory.homologyFunctor
        (RingedSpace.ClosedSubset.Modules X (Z : Set X)) (p + 1)).obj
        ((SectionsWithSupport.derived X Z).obj
          ((DerivedCategory.singleFunctor X.Modules 0).obj
            ((RingedSpace.ClosedSubset.pushforward X (Z : Set X)).obj M)))) := sorry

end AlgebraicGeometry.RingedSpace.ClosedSubset.Derived.Pushforward
