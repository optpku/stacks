/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.AlgebraicGeometry.AlgebraicSpace.Integral
public import ReasLib.AlgebraicGeometry.AlgebraicSpace.GlobalSections

/-!
# Global sections of integral algebraic spaces

The ring of global sections of an integral algebraic space is a domain.
-/

@[expose] public section

open CategoryTheory AlgebraicGeometry

noncomputable section

universe u

namespace AlgebraicGeometry.AlgebraicSpace

/-- The global-sections ring of an integral algebraic space is a domain. -/
instance instIsDomain_globalSectionsRing {S : Scheme.{u}} {X : AlgebraicSpace S}
    [IsIntegral X] : IsDomain (globalSectionsRing X) :=
  sorry

end AlgebraicGeometry.AlgebraicSpace
