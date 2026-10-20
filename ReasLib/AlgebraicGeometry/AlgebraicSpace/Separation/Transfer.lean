module

public import ReasLib.AlgebraicGeometry.AlgebraicSpace.Separation.Absolute
public import ReasLib.AlgebraicGeometry.AlgebraicSpace.Separation.Composition

/-!
# Transfer of separation axioms along morphisms of algebraic spaces

Separated, quasi-separated, and locally separated morphisms transfer the
corresponding absolute and relative separation properties from target to source.
-/

@[expose] public section

open CategoryTheory AlgebraicGeometry

universe u

namespace AlgebraicGeometry.AlgebraicSpace

/-- The source of a separated morphism to an absolutely separated algebraic space
is absolutely separated. -/
@[stacks 04ZH]
theorem IsAbsolutelySeparated.of_separated {S : Scheme.{u}} {X Y : AlgebraicSpace S}
    (f : X ⟶ Y) [IsAbsolutelySeparated Y] [Separated f] : IsAbsolutelySeparated X :=
  sorry

/-- The source of a quasi-separated morphism to an absolutely quasi-separated
algebraic space is absolutely quasi-separated. -/
@[stacks 04ZH]
theorem IsAbsolutelyQuasiSeparated.of_quasiSeparated {S : Scheme.{u}} {X Y : AlgebraicSpace S}
    (f : X ⟶ Y) [IsAbsolutelyQuasiSeparated Y] [QuasiSeparated f] :
    IsAbsolutelyQuasiSeparated X :=
  sorry

/-- The source of a locally separated morphism to an absolutely locally separated
algebraic space is absolutely locally separated. -/
@[stacks 04ZH]
theorem IsAbsolutelyLocallySeparated.of_locallySeparated {S : Scheme.{u}}
    {X Y : AlgebraicSpace S} (f : X ⟶ Y) [IsAbsolutelyLocallySeparated Y]
    [LocallySeparated f] : IsAbsolutelyLocallySeparated X :=
  sorry

/-- The source of a separated morphism to an algebraic space separated over the
base scheme is separated over the base scheme. -/
@[stacks 04ZH]
theorem IsSeparated.of_separated {S : Scheme.{u}} {X Y : AlgebraicSpace S} (f : X ⟶ Y)
    [IsSeparated Y] [Separated f] : IsSeparated X :=
  sorry

/-- The source of a quasi-separated morphism to an algebraic space quasi-separated
over the base scheme is quasi-separated over the base scheme. -/
@[stacks 04ZH]
theorem IsQuasiSeparated.of_quasiSeparated {S : Scheme.{u}} {X Y : AlgebraicSpace S}
    (f : X ⟶ Y) [IsQuasiSeparated Y] [QuasiSeparated f] : IsQuasiSeparated X :=
  sorry

/-- The source of a locally separated morphism to an algebraic space locally
separated over the base scheme is locally separated over the base scheme. -/
@[stacks 04ZH]
theorem IsLocallySeparated.of_locallySeparated {S : Scheme.{u}} {X Y : AlgebraicSpace S}
    (f : X ⟶ Y) [IsLocallySeparated Y] [LocallySeparated f] : IsLocallySeparated X :=
  sorry

end AlgebraicGeometry.AlgebraicSpace
