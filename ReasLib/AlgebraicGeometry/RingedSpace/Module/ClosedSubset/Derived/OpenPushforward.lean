module

public import ReasLib.AlgebraicGeometry.RingedSpace.Module.ClosedSubset.Derived
public import ReasLib.AlgebraicGeometry.RingedSpace.Module.OpenSubspace.Pushforward.Derived
import Mathlib.Tactic.CrossRefAttribute

/-!
# Closed support of derived pushforward from a disjoint open

For a bundled closed subset `Z` and an open `U` contained in its complement, this leaf records
the vanishing of derived sections with support in `Z` after derived pushforward from `U`.
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits TopologicalSpace

noncomputable section

universe u

namespace AlgebraicGeometry.RingedSpace.ClosedSubset.Derived.OpenPushforward

variable (X : RingedSpace.{u}) (U : Opens X.carrier) (Z : Closeds X)

/-- Derived local cohomology with support in `Z` after pushforward from `U`. -/
@[stacks 0G73 "closed support after derived open pushforward"]
abbrev localCohomology :
    moduleDerivedOnOpen X U ⥤ ModuleDerived X Z :=
  modulePushforwardFromOpenDerived U ⋙ SectionsWithSupport.derived X Z

/-- Disjointness of an open and a closed subset is equivalent to containment in the open
complement. -/
@[stacks 0G73 "disjoint open and closed subsets"]
theorem disjoint_iff_le_compl :
    Disjoint (U : Set X) (Z : Set X) ↔ U ≤ Z.compl := sorry

/-- Derived sections with support in `Z` vanish after pushforward from an open contained in the
complement of `Z`. -/
@[stacks 0G73 "closed-support vanishing after derived open pushforward"]
theorem isZero_of_le_compl (hUZ : U ≤ Z.compl) (K : moduleDerivedOnOpen X U) :
    IsZero ((localCohomology X U Z).obj K) := sorry

/-- Derived sections with support in `Z` vanish after pushforward from an open disjoint from
`Z`. -/
@[stacks 0G73 "closed-support vanishing after derived open pushforward"]
theorem isZero_of_disjoint
    (hUZ : Disjoint (U : Set X) (Z : Set X))
    (K : moduleDerivedOnOpen X U) :
    IsZero ((localCohomology X U Z).obj K) := sorry

end AlgebraicGeometry.RingedSpace.ClosedSubset.Derived.OpenPushforward
