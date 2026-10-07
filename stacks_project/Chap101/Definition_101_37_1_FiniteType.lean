module

public import stacks_project.Chap101.Definition_101_7_2_QuasiCompact
public import stacks_project.Chap101.Lemma_101_17_5_LocallyOfFiniteType

/-!
# Finite type morphisms of algebraic stacks

A morphism of algebraic stacks is of finite type when it is quasi-compact
and locally of finite type.
-/

@[expose] public section

open CategoryTheory AlgebraicGeometry
open scoped Bicategory

noncomputable section

universe u

namespace AlgebraicGeometry.AlgebraicStack

/-- A morphism of algebraic stacks is of finite type if it is quasi-compact
and locally of finite type. -/
@[mk_iff]
class FiniteType {S : Scheme.{u}} {X Y : GroupoidsOver S}
    [AlgebraicStack X] [AlgebraicStack Y] (f : X ⟶ Y) : Prop
    extends QuasiCompact f, LocallyOfFiniteType f

namespace FiniteType

/-- A finite-type morphism of algebraic stacks is quasi-compact and locally
of finite type. -/
theorem spec {S : Scheme.{u}} {X Y : GroupoidsOver S}
    [AlgebraicStack X] [AlgebraicStack Y] (f : X ⟶ Y) [FiniteType f] :
    QuasiCompact f ∧ LocallyOfFiniteType f :=
  sorry

/-- The identity morphism of an algebraic stack is of finite type. -/
instance id {S : Scheme.{u}} {X : GroupoidsOver S} [AlgebraicStack X] :
    FiniteType (𝟙 X) :=
  sorry

/-- An isomorphism of algebraic stacks is of finite type. -/
instance of_isIso {S : Scheme.{u}} {X Y : GroupoidsOver S}
    [AlgebraicStack X] [AlgebraicStack Y] (f : X ⟶ Y) [IsIso f] :
    FiniteType f :=
  sorry

/-- A quasi-compact morphism of algebraic stacks that is locally of finite
type is of finite type. -/
instance instOfQuasiCompactLocallyOfFiniteType {S : Scheme.{u}}
    {X Y : GroupoidsOver S} [AlgebraicStack X] [AlgebraicStack Y]
    (f : X ⟶ Y) [QuasiCompact f] [LocallyOfFiniteType f] : FiniteType f :=
  sorry

end FiniteType

end AlgebraicGeometry.AlgebraicStack
