module

public import stacks_project.Chap101.Lemma_101_7_8_Instances

/-!
# Fibre products of quasi-compact quasi-separated algebraic stacks

The apex of a 2-fibre product of algebraic stacks inherits quasi-compactness
from the two factors when the target is quasi-separated, and inherits
quasi-separatedness from the three stacks.
-/

@[expose] public section

open CategoryTheory AlgebraicGeometry
open Bicategory
open scoped Bicategory

universe u

namespace AlgebraicGeometry.AlgebraicStack

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

namespace IsQuasiSeparated

/-- The apex of a bilimit `PseudoPullbackCone` of algebraic stacks is
quasi-separated when the three stacks are quasi-separated. -/
theorem of_isBilimit {S : Scheme.{u}} {X Y Z : GroupoidsOver S}
    [AlgebraicStack X] [AlgebraicStack Y] [AlgebraicStack Z]
    {f : X ⟶ Y} {g : Z ⟶ Y}
    [IsQuasiSeparated X] [IsQuasiSeparated Y] [IsQuasiSeparated Z]
    (c : PseudoPullbackCone f g) [AlgebraicStack c.pt] (hc : c.IsBilimit) :
    IsQuasiSeparated c.pt :=
  sorry

/-- The chosen 2-fibre product of quasi-separated algebraic stacks is
quasi-separated. -/
instance (priority := low) instTwoFibreProduct {S : Scheme.{u}}
    {X Y Z : GroupoidsOver S}
    [AlgebraicStack X] [AlgebraicStack Y] [AlgebraicStack Z]
    (f : X ⟶ Y) (g : Z ⟶ Y)
    [IsQuasiSeparated X] [IsQuasiSeparated Y] [IsQuasiSeparated Z]
    [AlgebraicStack (TwoFibreProduct.apex.{u + 1, u, u + 1, u} f g)] :
    IsQuasiSeparated (TwoFibreProduct.apex.{u + 1, u, u + 1, u} f g) :=
  sorry

end IsQuasiSeparated

end AlgebraicGeometry.AlgebraicStack
