module

public import ReasLib.AlgebraicGeometry.RingedSpace.Module.ClosedSubset.Derived
public import ReasLib.AlgebraicGeometry.RingedSpace.Module.OpenSubspace.Pushforward.Derived
import Mathlib.Tactic.CrossRefAttribute

/-!
# Localization triangle for a closed subset

This leaf owns the module-level localization triangle attached to a bundled closed subset.  The
two maps are the counit of the closed-subset derived adjunction and the unit of the open
restriction/direct-image adjunction; the boundary is kept existential because no representative
is canonical at this interface.
-/

@[expose] public section

open CategoryTheory CategoryTheory.Pretriangulated TopologicalSpace

noncomputable section

universe u

namespace AlgebraicGeometry.RingedSpace.ClosedSubset.Derived.Localization

variable (X : RingedSpace.{u}) (Z : Closeds X)

/-- The closed-support term `R𝓗_Z ⋙ i_*` in the localization triangle. -/
@[stacks 0G72 "closed-support term in the module localization triangle"]
abbrev closedTerm : AlgebraicGeometry.RingedSpace.ModuleDerived X ⥤
    AlgebraicGeometry.RingedSpace.ModuleDerived X :=
  SectionsWithSupport.derived X Z ⋙ Pushforward.derived X Z

/-- The open-complement term `j_* ⋙ j^*` in the module localization triangle. -/
@[stacks 0G72 "open-complement term in the module localization triangle"]
abbrev openTerm : AlgebraicGeometry.RingedSpace.ModuleDerived X ⥤
    AlgebraicGeometry.RingedSpace.ModuleDerived X :=
  moduleRestrictionToOpenDerived X Z.compl ⋙
    modulePushforwardFromOpenDerived Z.compl

/-- The closed-support counit map in the module localization triangle. -/
@[stacks 0G72 "closed-support counit in the module localization triangle"]
abbrev closedMap : closedTerm X Z ⟶
    𝟭 (AlgebraicGeometry.RingedSpace.ModuleDerived X) :=
  (Derived.adjunction X Z).counit

/-- The open-complement restriction map in the module localization triangle. -/
@[stacks 0G72 "open-complement unit in the module localization triangle"]
abbrev openMap : 𝟭 (AlgebraicGeometry.RingedSpace.ModuleDerived X) ⟶ openTerm X Z :=
  (OpenSubspace.Pushforward.derivedAdjunction X Z.compl).unit

/-- The shifted closed-support term used as the third vertex of the localization triangle. -/
@[stacks 0G72 "shifted closed-support term in the module localization triangle"]
abbrev shifted : AlgebraicGeometry.RingedSpace.ModuleDerived X ⥤
    AlgebraicGeometry.RingedSpace.ModuleDerived X :=
  closedTerm X Z ⋙ shiftFunctor (AlgebraicGeometry.RingedSpace.ModuleDerived X) (1 : ℤ)

/-- A natural transformation is a module localization boundary when each component completes the
closed-support counit and open-complement unit to a distinguished triangle. -/
@[stacks 0G72 "module localization boundary"]
def IsBoundary (δ : openTerm X Z ⟶ shifted X Z) : Prop :=
  ∀ K : AlgebraicGeometry.RingedSpace.ModuleDerived X,
    Triangle.mk
        ((closedMap X Z).app K)
        ((openMap X Z).app K)
        (δ.app K) ∈ distTriang (AlgebraicGeometry.RingedSpace.ModuleDerived X)

/-- A functorial module localization boundary exists for every bundled closed subset. -/
@[stacks 0G72 "module localization triangle"]
theorem exists_boundary :
    ∃ δ : openTerm X Z ⟶ shifted X Z, IsBoundary X Z δ := sorry

/-- Objectwise module localization triangle for a bundled closed subset. -/
@[stacks 0G72 "objectwise module localization triangle"]
theorem triangle (K : AlgebraicGeometry.RingedSpace.ModuleDerived X) :
    ∃ δ : (openTerm X Z).obj K ⟶ (shifted X Z).obj K,
      Triangle.mk
          ((closedMap X Z).app K)
          ((openMap X Z).app K)
          δ ∈ distTriang (AlgebraicGeometry.RingedSpace.ModuleDerived X) := sorry

end AlgebraicGeometry.RingedSpace.ClosedSubset.Derived.Localization
