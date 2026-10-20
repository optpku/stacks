module

public import stacks_project.Chap101.Definition_101_7_2_QuasiCompact
public import stacks_project.Chap101.Lemma_101_17_5_LocallyOfFiniteType
public import ReasLib.AlgebraicGeometry.AlgebraicStack.FiniteType

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

#check (AlgebraicGeometry.AlgebraicStack.FiniteType :
  ∀ {S : Scheme.{u}} {X Y : GroupoidsOver S}
    [AlgebraicStack X] [AlgebraicStack Y], (X ⟶ Y) → Prop)

#check (AlgebraicGeometry.AlgebraicStack.finiteType_iff :
  ∀ {S : Scheme.{u}} {X Y : GroupoidsOver S}
    [AlgebraicStack X] [AlgebraicStack Y] (f : X ⟶ Y),
    FiniteType f ↔ QuasiCompact f ∧ LocallyOfFiniteType f)

#check (AlgebraicGeometry.AlgebraicStack.FiniteType.spec :
  ∀ {S : Scheme.{u}} {X Y : GroupoidsOver S}
    [AlgebraicStack X] [AlgebraicStack Y] (f : X ⟶ Y) [FiniteType f],
    QuasiCompact f ∧ LocallyOfFiniteType f)

#check (AlgebraicGeometry.AlgebraicStack.FiniteType.id :
  ∀ {S : Scheme.{u}} {X : GroupoidsOver S} [AlgebraicStack X],
    FiniteType (𝟙 X))

#check (AlgebraicGeometry.AlgebraicStack.FiniteType.of_isIso :
  ∀ {S : Scheme.{u}} {X Y : GroupoidsOver S}
    [AlgebraicStack X] [AlgebraicStack Y] (f : X ⟶ Y) [IsIso f],
    FiniteType f)

#check (AlgebraicGeometry.AlgebraicStack.FiniteType.instOfQuasiCompactLocallyOfFiniteType :
  ∀ {S : Scheme.{u}} {X Y : GroupoidsOver S}
    [AlgebraicStack X] [AlgebraicStack Y] (f : X ⟶ Y)
    [QuasiCompact f] [LocallyOfFiniteType f], FiniteType f)

end AlgebraicGeometry.AlgebraicStack
