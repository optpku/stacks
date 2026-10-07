module

public import ReasLib.Algebra.Category.ModuleCat.Sheaf.ClosedSubset.Derived.Supported
public import ReasLib.AlgebraicGeometry.RingedSpace.Module.ClosedSubset.Derived
public import ReasLib.AlgebraicGeometry.RingedSpace.Module.Derived.Support
import Mathlib.Tactic.CrossRefAttribute

/-!
# Derived modules supported on a closed subset of a ringed space

This file gives the coefficient-generic supported-derived equivalence and coreflection their
ringed-space vocabulary.  All mathematical constructions are owned by
`SheafOfModules.ClosedSubset`.
-/

@[expose] public section

open CategoryTheory TopologicalSpace

noncomputable section

universe u

namespace AlgebraicGeometry.RingedSpace.ClosedSubset

variable (X : RingedSpace.{u}) (Z : Closeds X)

/-- The full subcategory of derived `𝒪_X`-modules whose cohomology is supported on `Z`. -/
@[stacks 0AEF "ringed-space supported derived modules"]
abbrev SupportedDerived :=
  RingedSpace.ModuleDerived.SupportedOn (X := X) (Z : Set X)

namespace Derived.Pushforward

/-- Derived direct image from `Z`, with codomain restricted to supported derived modules. -/
@[stacks 0AEF "ringed-space pushforward to supported derived modules"]
noncomputable abbrev toSupported :
    ModuleDerived X Z ⥤ SupportedDerived X Z :=
  SheafOfModules.ClosedSubset.Derived.Pushforward.toSupported X.ringCatSheaf Z

end Derived.Pushforward

namespace SupportedDerived

/-- The inclusion of supported derived modules into all derived `𝒪_X`-modules. -/
@[stacks 0AEF "ringed-space supported derived inclusion"]
abbrev inclusion : ClosedSubset.SupportedDerived X Z ⥤ RingedSpace.ModuleDerived X :=
  RingedSpace.ModuleDerived.SupportedOn.inclusion (X := X) (Z : Set X)

/-- The coreflector onto supported derived modules. -/
@[stacks 0AEF "ringed-space supported derived coreflector"]
noncomputable abbrev coreflector :
    RingedSpace.ModuleDerived X ⥤ ClosedSubset.SupportedDerived X Z :=
  SheafOfModules.ClosedSubset.SupportedDerived.coreflector X.ringCatSheaf Z

/-- The coreflection adjunction for derived `𝒪_X`-modules supported on `Z`. -/
@[stacks 0AEF "ringed-space supported derived coreflection"]
noncomputable abbrev adjunction : inclusion X Z ⊣ coreflector X Z :=
  SheafOfModules.ClosedSubset.SupportedDerived.adjunction X.ringCatSheaf Z

end SupportedDerived

#synth Coreflective (SupportedDerived.inclusion X Z)
#synth (Derived.Pushforward.toSupported X Z).IsEquivalence

end AlgebraicGeometry.RingedSpace.ClosedSubset
