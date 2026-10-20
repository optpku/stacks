module

public import ReasLib.AlgebraicGeometry.AlgebraicStack.Submersive

/-!
# Base change of universally submersive morphisms of algebraic stacks

Universally submersive morphisms of algebraic stacks remain universally
submersive under arbitrary algebraic-stack base change.
-/

@[expose] public section

open CategoryTheory AlgebraicGeometry
open Bicategory
open scoped Bicategory

noncomputable section

universe u

namespace AlgebraicGeometry.AlgebraicStack

namespace UniversallySubmersive

/-- Universally submersive morphisms of algebraic stacks remain universally
submersive along the second projection of any bilimit `PseudoPullbackCone`. -/
theorem of_isBilimit {S : Scheme.{u}} {X Y Z : GroupoidsOver S}
    [AlgebraicStack X] [AlgebraicStack Y] [AlgebraicStack Z]
    {f : X ⟶ Y} {g : Z ⟶ Y} [UniversallySubmersive f]
    (c : PseudoPullbackCone f g) [AlgebraicStack c.pt] (hc : c.IsBilimit) :
    UniversallySubmersive c.snd :=
  sorry

/-- The first projection of a chosen 2-fibre product is universally submersive
whenever the second leg is a universally submersive morphism of algebraic
stacks. -/
instance twoFibreProduct_fst {S : Scheme.{u}} {X Y Z : GroupoidsOver S}
    [AlgebraicStack X] [AlgebraicStack Y] [AlgebraicStack Z]
    (f : X ⟶ Y) (g : Z ⟶ Y) [UniversallySubmersive g] :
    UniversallySubmersive (TwoFibreProduct.fst.{u + 1, u, u + 1, u} f g) :=
  sorry

end UniversallySubmersive

/-- The second projection of a chosen 2-fibre product is universally submersive
whenever the first leg is a universally submersive morphism of algebraic
stacks. -/
instance universallySubmersive_pullback_snd {S : Scheme.{u}}
    {X Y Z : GroupoidsOver S} [AlgebraicStack X] [AlgebraicStack Y]
    [AlgebraicStack Z] (f : X ⟶ Y) (g : Z ⟶ Y) [UniversallySubmersive f] :
    UniversallySubmersive (TwoFibreProduct.snd.{u + 1, u, u + 1, u} f g) :=
  sorry

end AlgebraicGeometry.AlgebraicStack
