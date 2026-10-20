module

public import ReasLib.AlgebraicGeometry.AlgebraicStack.LocallyQuasiFinite

/-!
# Base change of locally quasi-finite morphisms of algebraic stacks

Locally quasi-finite morphisms of algebraic stacks and morphisms with discrete
field fibers are stable under base change.
-/

@[expose] public section

open CategoryTheory AlgebraicGeometry
open Bicategory
open scoped Bicategory

noncomputable section

universe u

namespace AlgebraicGeometry.AlgebraicStack.discreteFieldFibers

/-- Discrete field fibers of a morphism of algebraic stacks are inherited by
the second projection of any bilimit `PseudoPullbackCone`. -/
theorem of_isBilimit {S : Scheme.{u}} {X Y Z : GroupoidsOver S}
    [AlgebraicStack X] [AlgebraicStack Y] [AlgebraicStack Z]
    {f : X ⟶ Y} {g : Z ⟶ Y} (hf : discreteFieldFibers f)
    (c : PseudoPullbackCone f g) [AlgebraicStack c.pt] (hc : c.IsBilimit) :
    discreteFieldFibers c.snd := sorry

end AlgebraicGeometry.AlgebraicStack.discreteFieldFibers

namespace AlgebraicGeometry.AlgebraicStack.LocallyQuasiFinite

/-- Locally quasi-finite morphisms of algebraic stacks remain locally
quasi-finite along the second projection of any bilimit `PseudoPullbackCone`. -/
theorem of_isBilimit {S : Scheme.{u}} {X Y Z : GroupoidsOver S}
    [AlgebraicStack X] [AlgebraicStack Y] [AlgebraicStack Z]
    {f : X ⟶ Y} {g : Z ⟶ Y} [LocallyQuasiFinite f]
    (c : PseudoPullbackCone f g) [AlgebraicStack c.pt] (hc : c.IsBilimit) :
    LocallyQuasiFinite c.snd := sorry

/-- The first projection of a chosen 2-fibre product is locally quasi-finite
whenever the second leg is a locally quasi-finite morphism of algebraic
stacks. -/
instance twoFibreProduct_fst {S : Scheme.{u}} {X Y Z : GroupoidsOver S}
    [AlgebraicStack X] [AlgebraicStack Y] [AlgebraicStack Z]
    (f : X ⟶ Y) (g : Z ⟶ Y) [LocallyQuasiFinite g]
    [AlgebraicStack (TwoFibreProduct.apex.{u + 1, u, u + 1, u} f g)] :
    LocallyQuasiFinite (TwoFibreProduct.fst.{u + 1, u, u + 1, u} f g) := sorry

/-- The second projection of a chosen 2-fibre product is locally quasi-finite
whenever the first leg is a locally quasi-finite morphism of algebraic
stacks. -/
@[stacks 06UB]
instance twoFibreProduct_snd {S : Scheme.{u}} {X Y Z : GroupoidsOver S}
    [AlgebraicStack X] [AlgebraicStack Y] [AlgebraicStack Z]
    (f : X ⟶ Y) (g : Z ⟶ Y) [LocallyQuasiFinite f]
    [AlgebraicStack (TwoFibreProduct.apex.{u + 1, u, u + 1, u} f g)] :
    LocallyQuasiFinite (TwoFibreProduct.snd.{u + 1, u, u + 1, u} f g) :=
  sorry

end AlgebraicGeometry.AlgebraicStack.LocallyQuasiFinite
