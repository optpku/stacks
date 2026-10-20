/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.AlgebraicGeometry.AlgebraicSpace.Normal
public import ReasLib.AlgebraicGeometry.AlgebraicSpace.Integral
public import ReasLib.AlgebraicGeometry.AlgebraicSpace.GlobalSections

/-!
# Global sections of a normal integral algebraic space

The ring of global sections of a normal integral algebraic space is a normal domain.
-/

@[expose] public section

open AlgebraicGeometry

universe u

namespace AlgebraicGeometry.AlgebraicSpace

/-- The ring of global sections of a normal integral algebraic space is a domain and a
normal ring. -/
@[stacks 0BH3]
theorem isNormalDomain_globalSectionsRing {S : Scheme.{u}} {X : AlgebraicSpace S}
    [IsNormal X] [IsIntegral X] :
    IsDomain (globalSectionsRing X) ∧ IsNormalRing (globalSectionsRing X) :=
  sorry

/-- The ring of global sections of a normal integral algebraic space is normal. -/
instance instIsNormalRing_globalSectionsRing {S : Scheme.{u}} {X : AlgebraicSpace S}
    [IsNormal X] [IsIntegral X] : IsNormalRing (globalSectionsRing X) :=
  (isNormalDomain_globalSectionsRing (X := X)).2

end AlgebraicGeometry.AlgebraicSpace
