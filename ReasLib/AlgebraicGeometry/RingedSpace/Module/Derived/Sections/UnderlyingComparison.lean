/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import ReasLib.AlgebraicGeometry.RingedSite.Module.GlobalSections.Derived.UnderlyingSectionsComparison
public import ReasLib.AlgebraicGeometry.RingedSpace.Module.Derived.Sections
public import ReasLib.AlgebraicGeometry.RingedSpace.Module.OpensRingedSite
import Mathlib.Tactic.CrossRefAttribute

/-!
# Underlying-additive derived sections

This facade exposes the concrete natural isomorphism already owned by the opens-ringed-site layer.
The source-facing `isomorphic` bridge keeps the cochain-derived RingedSpace notation available,
while `comparisonIso` and `appIso` are the canonical functor/object interfaces for downstream use.
-/

@[expose] public section

open AlgebraicGeometry CategoryTheory Opposite TopologicalSpace

noncomputable section

universe u

namespace AlgebraicGeometry.RingedSpace.Module.Derived.Sections.UnderlyingComparison

variable {X : RingedSpace.{u}}

/-- The canonical opens-site source of the underlying-additive section comparison. -/
@[stacks 0D5Y "underlying-additive derived sections source"]
abbrev canonicalSource (X : RingedSpace.{u}) (U : Opens X.carrier) :
    ModuleDerived X ⥤ DerivedCategory AddCommGrpCat.{u} :=
  RingedSite.Hom.ModuleSections.sectionsSourceDerived X.opensRingedSite U

/-- The canonical opens-site target of the underlying-additive section comparison. -/
@[stacks 0D5Y "underlying-additive derived sections target"]
abbrev canonicalTarget (X : RingedSpace.{u}) (U : Opens X.carrier) :
    ModuleDerived X ⥤ DerivedCategory AddCommGrpCat.{u} :=
  RingedSite.Hom.ModuleSections.sectionsTargetDerived X.opensRingedSite U

/-- The functor-level underlying-additive derived section comparison. -/
@[stacks 0D5Y "underlying-additive derived sections comparison"]
noncomputable def comparisonIso (X : RingedSpace.{u}) (U : Opens X.carrier) :
    canonicalSource X U ≅ canonicalTarget X U :=
  RingedSite.Hom.ModuleSections.sectionsIso X.opensRingedSite U

/-- The objectwise component of the underlying-additive derived section comparison. -/
@[stacks 0D5Y "underlying-additive derived sections component"]
noncomputable def appIso (X : RingedSpace.{u}) (U : Opens X.carrier)
    (K : ModuleDerived X) :
    (canonicalSource X U).obj K ≅ (canonicalTarget X U).obj K :=
  (comparisonIso X U).app K

/-- The source-facing RingedSpace formulation of the derived section comparison. -/
@[stacks 0D5Y "derived sections agree after forgetting module structure"]
theorem isomorphic (X : RingedSpace.{u}) (U : Opens X.carrier)
    [IsGrothendieckAbelian X.Modules] :
    IsIsomorphic
      (moduleDerivedSectionsAtOpenToAb X U)
      (moduleSectionsAsAbelianDerived X U) := sorry

end AlgebraicGeometry.RingedSpace.Module.Derived.Sections.UnderlyingComparison

end
