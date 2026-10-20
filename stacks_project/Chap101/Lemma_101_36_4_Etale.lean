module

public import ReasLib.AlgebraicGeometry.AlgebraicStack.Etale

/-!
# Étale morphisms of algebraic stacks
-/

@[expose] public section

open CategoryTheory AlgebraicGeometry
open scoped Bicategory

universe u

#check (AlgebraicGeometry.AlgebraicSpace.Etale.isEtaleSmoothLocalAtSourceAndTarget :
  ∀ {S : Scheme.{u}},
    AlgebraicSpace.IsEtaleSmoothLocalAtSourceAndTarget (@AlgebraicSpace.Etale S))

namespace AlgebraicGeometry.AlgebraicStack

#check (AlgebraicGeometry.AlgebraicStack.Etale :
  ∀ {S : Scheme.{u}} {X Y : GroupoidsOver S} [AlgebraicStack X] [AlgebraicStack Y],
    (X ⟶ Y) → Prop)

#check (AlgebraicGeometry.AlgebraicStack.etale_iff :
  ∀ {S : Scheme.{u}} {X Y : GroupoidsOver S} [AlgebraicStack X] [AlgebraicStack Y]
    (f : X ⟶ Y),
    Etale f ↔
      DM f ∧ hasEtaleSmoothLocalAtSourceAndTarget (@AlgebraicSpace.Etale S) f)

#check (AlgebraicGeometry.AlgebraicStack.Etale.id :
  ∀ {S : Scheme.{u}} {X : GroupoidsOver S} [AlgebraicStack X], Etale (𝟙 X))

#check (AlgebraicGeometry.AlgebraicStack.Etale.spec :
  ∀ {S : Scheme.{u}} {X Y : GroupoidsOver S} [AlgebraicStack X] [AlgebraicStack Y]
    (f : X ⟶ Y) [Etale f],
    hasEtaleSmoothLocalAtSourceAndTarget (@AlgebraicSpace.Etale S) f)

end AlgebraicGeometry.AlgebraicStack
