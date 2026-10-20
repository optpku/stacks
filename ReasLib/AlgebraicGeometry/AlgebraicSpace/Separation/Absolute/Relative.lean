/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.AlgebraicGeometry.AlgebraicSpace.Separation.Absolute

/-!
# Relative separation properties of absolutely separated algebraic spaces

Absolute separatedness, local separatedness, and quasi-separatedness of an algebraic
space imply the corresponding relative property over any scheme serving as its base.
-/

@[expose] public section

universe u

namespace AlgebraicGeometry.AlgebraicSpace

namespace IsSeparated

/-- An absolutely separated algebraic space is separated over its base. -/
instance (priority := 900) of_isAbsolutelySeparated {S : Scheme.{u}} (X : AlgebraicSpace S)
    [IsAbsolutelySeparated X] : IsSeparated X := sorry

end IsSeparated

namespace IsLocallySeparated

/-- An absolutely locally separated algebraic space is locally separated over its base. -/
instance (priority := 900) of_isAbsolutelyLocallySeparated {S : Scheme.{u}}
    (X : AlgebraicSpace S) [IsAbsolutelyLocallySeparated X] : IsLocallySeparated X :=
  sorry

end IsLocallySeparated

/-- An absolutely quasi-separated algebraic space over a scheme is quasi-separated
relative to that scheme. -/
instance instIsQuasiSeparated_of_isAbsolutelyQuasiSeparated {S : Scheme.{u}}
    (X : AlgebraicSpace S) [IsAbsolutelyQuasiSeparated X] : IsQuasiSeparated X := sorry

end AlgebraicGeometry.AlgebraicSpace
