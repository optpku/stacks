module

public import ReasLib.AlgebraicGeometry.AlgebraicStack.Morphism.QuasiCompact
public import ReasLib.AlgebraicGeometry.AlgebraicStack.QuasiSeparated

/-!
# Quasi-compactness permanence for algebraic stacks

Morphisms from quasi-compact algebraic stacks to quasi-separated algebraic
stacks are quasi-compact. Fibre products of quasi-compact algebraic stacks
over a quasi-separated target are quasi-compact.
-/

@[expose] public section

open CategoryTheory AlgebraicGeometry
open Bicategory
open scoped Bicategory

universe u

namespace AlgebraicGeometry.AlgebraicStack

namespace QuasiCompact

/-- A morphism of algebraic stacks from a quasi-compact source to a
quasi-separated target is quasi-compact. -/
instance (priority := low) of_isQuasiCompact {S : Scheme.{u}} {X Y : GroupoidsOver S}
    [AlgebraicStack X] [AlgebraicStack Y] (f : X ⟶ Y)
    [IsQuasiCompact X] [IsQuasiSeparated Y] : QuasiCompact f :=
  sorry

end QuasiCompact

namespace IsQuasiCompact

/-- The apex of a bilimit `PseudoPullbackCone` of algebraic stacks is
quasi-compact when the two factors are quasi-compact and the target is
quasi-separated. -/
theorem of_isBilimit {S : Scheme.{u}} {X Y Z : GroupoidsOver S}
    [AlgebraicStack X] [AlgebraicStack Y] [AlgebraicStack Z]
    {f : X ⟶ Y} {g : Z ⟶ Y}
    [IsQuasiCompact X] [IsQuasiSeparated Y] [IsQuasiCompact Z]
    (c : PseudoPullbackCone f g) [AlgebraicStack c.pt] (hc : c.IsBilimit) :
    IsQuasiCompact c.pt :=
  sorry

/-- The chosen 2-fibre product of quasi-compact algebraic stacks over a
quasi-separated target is quasi-compact. -/
instance (priority := low) instTwoFibreProduct {S : Scheme.{u}}
    {X Y Z : GroupoidsOver S}
    [AlgebraicStack X] [AlgebraicStack Y] [AlgebraicStack Z]
    (f : X ⟶ Y) (g : Z ⟶ Y)
    [IsQuasiCompact X] [IsQuasiSeparated Y] [IsQuasiCompact Z]
    [AlgebraicStack (TwoFibreProduct.apex.{u + 1, u, u + 1, u} f g)] :
    IsQuasiCompact (TwoFibreProduct.apex.{u + 1, u, u + 1, u} f g) :=
  sorry

end IsQuasiCompact

end AlgebraicGeometry.AlgebraicStack
