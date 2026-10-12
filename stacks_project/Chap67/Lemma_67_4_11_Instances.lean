/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import stacks_project.Chap66.Definition_66_3_1_Separation
public import stacks_project.Chap67.Definition_67_4_2_Separation

/-!
# Absolute and relative separation implications

An absolutely separated, locally separated, or quasi-separated algebraic space is
separated, locally separated, or quasi-separated over its base. A morphism out of a
relatively separated, locally separated, or quasi-separated algebraic space inherits
the corresponding morphism property.
-/

@[expose] public section

open CategoryTheory AlgebraicGeometry

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

namespace IsQuasiSeparated

/-- An absolutely quasi-separated algebraic space is quasi-separated over its base. -/
instance (priority := 900) of_isAbsolutelyQuasiSeparated {S : Scheme.{u}}
    (X : AlgebraicSpace S) [IsAbsolutelyQuasiSeparated X] : IsQuasiSeparated X :=
  sorry

end IsQuasiSeparated

namespace Separated

/-- A morphism of algebraic spaces out of a relatively separated source is separated. -/
instance (priority := 900) of_isSeparated {S : Scheme.{u}} {X Y : AlgebraicSpace S}
    (f : X ⟶ Y) [IsSeparated X] : Separated f := sorry

end Separated

namespace LocallySeparated

/-- A morphism of algebraic spaces out of a relatively locally separated source is locally
separated. -/
instance (priority := 900) of_isLocallySeparated {S : Scheme.{u}} {X Y : AlgebraicSpace S}
    (f : X ⟶ Y) [IsLocallySeparated X] : LocallySeparated f := sorry

end LocallySeparated

namespace QuasiSeparated

/-- A morphism of algebraic spaces out of a relatively quasi-separated source is
quasi-separated. -/
instance (priority := 900) of_isQuasiSeparated {S : Scheme.{u}} {X Y : AlgebraicSpace S}
    (f : X ⟶ Y) [IsQuasiSeparated X] : QuasiSeparated f := sorry

end QuasiSeparated

end AlgebraicGeometry.AlgebraicSpace
