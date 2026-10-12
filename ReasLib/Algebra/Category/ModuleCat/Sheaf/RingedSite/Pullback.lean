/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import ReasLib.Algebra.Category.ModuleCat.Sheaf.RingedSite.Pullback.FinitePresentation
public import ReasLib.Algebra.Category.ModuleCat.Sheaf.RingedSite.Pullback.LocalGeneration
public import ReasLib.Algebra.Category.ModuleCat.Sheaf.RingedSite.Pullback.LocallyFree
public import ReasLib.Algebra.Category.ModuleCat.Sheaf.RingedSite.Pullback.Quasicoherent

/-!
# Pullback Properties of Module Sheaves on Ringed Sites

Convenience import for the property-specific inverse-image preservation leaves.
For functor computation and naturality, use Mathlib's
`SheafOfModules.pullbackId`, `SheafOfModules.pullbackComp`, and
`SheafOfModules.pullback_assoc` directly.
-/
