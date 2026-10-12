/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import ReasLib.AlgebraicGeometry.Scheme.Morphism.FinitePresentation.Cancellation

/-!
# Diagonals of finite presentation morphisms

The diagonal of a locally finite type scheme morphism is locally of finite presentation. Under
quasi-separatedness, the diagonal is of finite presentation.
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits

universe u

namespace AlgebraicGeometry

/-- The diagonal of a locally finite type morphism of schemes is locally of finite presentation. -/
@[instance]
theorem locallyOfFinitePresentation_diagonal_of_locallyOfFiniteType
    {X Y : Scheme.{u}} (f : X ⟶ Y) [LocallyOfFiniteType f] :
    LocallyOfFinitePresentation (pullback.diagonal f) := sorry

namespace Scheme.Hom

/-- The diagonal of a quasi-separated locally finite type morphism of schemes is of finite
presentation. -/
@[instance]
theorem finitePresentation_diagonal_of_quasiSeparated_of_locallyOfFiniteType
    {X Y : Scheme.{u}} (f : X ⟶ Y) [QuasiSeparated f] [LocallyOfFiniteType f] :
    FinitePresentation (pullback.diagonal f) := sorry

end Scheme.Hom
end AlgebraicGeometry
