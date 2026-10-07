module

public import stacks_project.Chap67.Definition_67_8_2_QuasiCompact
public import stacks_project.Chap66.Definition_66_3_1_Separation
public import stacks_project.Chap67.Definition_67_4_2_Separation

/-!
# Quasi-compact and quasi-separated morphisms from space properties

A morphism of algebraic spaces out of a quasi-compact source into a
quasi-separated target is quasi-compact. A morphism out of an absolutely
quasi-separated source is quasi-separated.
-/

@[expose] public section

open CategoryTheory AlgebraicGeometry

universe u

namespace AlgebraicGeometry.AlgebraicSpace

namespace QuasiCompact

/-- A morphism of algebraic spaces from a quasi-compact source to a quasi-separated
target is quasi-compact. -/
instance (priority := low) of_isQuasiCompact {S : Scheme.{u}} {X Y : AlgebraicSpace S}
    (f : X ⟶ Y) [IsQuasiCompact X] [IsAbsolutelyQuasiSeparated Y] : QuasiCompact f :=
  sorry

end QuasiCompact

namespace QuasiSeparated

/-- A morphism of algebraic spaces out of an absolutely quasi-separated source is
quasi-separated. -/
instance (priority := low) of_isAbsolutelyQuasiSeparated {S : Scheme.{u}}
    {X Y : AlgebraicSpace S} (f : X ⟶ Y) [IsAbsolutelyQuasiSeparated X] :
    QuasiSeparated f :=
  sorry

end QuasiSeparated

end AlgebraicGeometry.AlgebraicSpace
