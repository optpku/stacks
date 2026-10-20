module

public import ReasLib.AlgebraicGeometry.AlgebraicStack.Separation
public import ReasLib.AlgebraicGeometry.AlgebraicStack.Closed
public import ReasLib.AlgebraicGeometry.AlgebraicStack.FiniteType

/-!
# Proper morphisms of algebraic stacks

A morphism of algebraic stacks is proper when it is separated, of finite
type, and universally closed.
-/

@[expose] public section

open CategoryTheory AlgebraicGeometry
open scoped Bicategory

noncomputable section

universe u

namespace AlgebraicGeometry.AlgebraicStack

/-- A morphism of algebraic stacks is proper if it is separated, of finite
type, and universally closed. -/
@[mk_iff]
class Proper {S : Scheme.{u}} {X Y : GroupoidsOver S}
    [AlgebraicStack X] [AlgebraicStack Y] (f : X ⟶ Y) : Prop
    extends Separated f, FiniteType f, UniversallyClosed f

namespace Proper

/-- A proper morphism of algebraic stacks is separated, of finite type, and
universally closed. -/
theorem spec {S : Scheme.{u}} {X Y : GroupoidsOver S}
    [AlgebraicStack X] [AlgebraicStack Y] (f : X ⟶ Y) [Proper f] :
    Separated f ∧ FiniteType f ∧ UniversallyClosed f :=
  sorry

/-- The identity morphism of an algebraic stack is proper. -/
instance id {S : Scheme.{u}} {X : GroupoidsOver S} [AlgebraicStack X] :
    Proper (𝟙 X) :=
  sorry

/-- An isomorphism of algebraic stacks is proper. -/
instance of_isIso {S : Scheme.{u}} {X Y : GroupoidsOver S}
    [AlgebraicStack X] [AlgebraicStack Y] (f : X ⟶ Y) [IsIso f] :
    Proper f :=
  sorry

/-- A separated, finite type, and universally closed morphism of algebraic
stacks is proper. -/
instance instOfSeparatedFiniteTypeUniversallyClosed {S : Scheme.{u}}
    {X Y : GroupoidsOver S} [AlgebraicStack X] [AlgebraicStack Y]
    (f : X ⟶ Y) [Separated f] [FiniteType f] [UniversallyClosed f] :
    Proper f :=
  sorry

/-- A proper morphism of algebraic spaces induces a proper 1-morphism of
algebraic stacks. -/
instance of_toGroupoids {S : Scheme.{u}} {X Y : AlgebraicSpace S} (f : X ⟶ Y)
    [AlgebraicSpace.Proper f] :
    Proper (AlgebraicSpace.toGroupoids.map f) :=
  sorry

end Proper

end AlgebraicGeometry.AlgebraicStack
