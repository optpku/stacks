module

public import ReasLib.AlgebraicGeometry.AlgebraicStack.Separation
public import ReasLib.AlgebraicGeometry.GroupoidsOver.Monomorphism
public import ReasLib.AlgebraicGeometry.GroupoidsOver.Immersion

/-!
# Separation properties of monomorphisms and immersions of algebraic stacks

Monomorphisms and immersions of algebraic stacks are separated and DM.
-/

@[expose] public section

open CategoryTheory AlgebraicGeometry
open scoped Bicategory

universe u

namespace AlgebraicGeometry.AlgebraicStack

namespace Separated

/-- A monomorphism of algebraic stacks is separated. -/
instance of_mono {S : Scheme.{u}} {X Y : GroupoidsOver S}
    [AlgebraicStack X] [AlgebraicStack Y] (f : X ⟶ Y)
    [Groupoids.Hom.Mono f] :
    Separated f :=
  sorry

/-- An immersion of algebraic stacks is separated. -/
instance of_immersion {S : Scheme.{u}} {X Y : GroupoidsOver S}
    [AlgebraicStack X] [AlgebraicStack Y] (f : X ⟶ Y)
    [Groupoids.Hom.Immersion f] :
    Separated f :=
  sorry

end Separated

namespace DM

/-- A monomorphism of algebraic stacks is DM. -/
instance of_mono {S : Scheme.{u}} {X Y : GroupoidsOver S}
    [AlgebraicStack X] [AlgebraicStack Y] (f : X ⟶ Y)
    [Groupoids.Hom.Mono f] :
    DM f :=
  sorry

/-- An immersion of algebraic stacks is DM. -/
instance of_immersion {S : Scheme.{u}} {X Y : GroupoidsOver S}
    [AlgebraicStack X] [AlgebraicStack Y] (f : X ⟶ Y)
    [Groupoids.Hom.Immersion f] :
    DM f :=
  sorry

end DM

end AlgebraicGeometry.AlgebraicStack
