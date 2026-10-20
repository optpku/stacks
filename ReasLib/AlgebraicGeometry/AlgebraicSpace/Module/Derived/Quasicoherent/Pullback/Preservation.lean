/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.AlgebraicGeometry.AlgebraicSpace.Module.Derived.Pullback.Basic

/-! # Preservation of quasi-coherent cohomology by derived pullback -/

@[expose] public section

open CategoryTheory

universe u

namespace AlgebraicGeometry.AlgebraicSpace.ModuleDerived

/-- Derived inverse image along an arbitrary morphism of algebraic spaces preserves
quasi-coherent cohomology. -/
theorem pullback_preservesQuasiCoherent {S : Scheme.{u}} {Y X : AlgebraicSpace S}
    (f : Y ⟶ X) :
    derivedQuasiCoherentModuleProperty X ≤
      (derivedQuasiCoherentModuleProperty Y).inverseImage (ModuleDerived.pullback f) := sorry

end AlgebraicGeometry.AlgebraicSpace.ModuleDerived
