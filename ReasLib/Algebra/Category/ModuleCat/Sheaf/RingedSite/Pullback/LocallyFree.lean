/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import Mathlib.Algebra.Category.ModuleCat.Sheaf.PullbackContinuous
public import ReasLib.Algebra.Category.ModuleCat.Sheaf.FiniteLocallyFree
public import ReasLib.Algebra.Category.ModuleCat.Sheaf.PullbackContinuous.LocallyFree

/-!
# Pullback of Locally Free Sheaves of Modules

Local freeness and finite local freeness are preserved by the canonical inverse-image functor
attached to a continuous representably flat functor and a morphism of ring sheaves. Neither
property requires commutativity of the rings.
-/

/-!
The property-preservation instances are owned by
`SheafOfModules` in `Sheaf/PullbackContinuous/LocallyFree`.  This legacy import
path is retained for modules that still import it directly, but it defines no
`SheafOfModules.RingedSite` aliases.
-/
