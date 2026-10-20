module

public import ReasLib.AlgebraicGeometry.AlgebraicSpace.Thickening.FiniteOrder
import StacksCheckRecall

open CategoryTheory

universe u

/- Definition 76.9.1: a finite-order thickening is a closed immersion with
nilpotent defining ideal sheaf. -/
@[stacks 05ZK] #check (AlgebraicGeometry.AlgebraicSpace.IsFiniteOrderThickening :
  {S : AlgebraicGeometry.Scheme.{u}} →
    {X X' : AlgebraicGeometry.AlgebraicSpace S} → (X ⟶ X') → Prop)

#check (AlgebraicGeometry.AlgebraicSpace.IsNthOrderThickening :
  ℕ → {S : AlgebraicGeometry.Scheme.{u}} →
    {X X' : AlgebraicGeometry.AlgebraicSpace S} → (X ⟶ X') → Prop)

#check (AlgebraicGeometry.AlgebraicSpace.IdealSubobject.pow_eq_bot :
  {S : AlgebraicGeometry.Scheme.{u}} →
    {X : AlgebraicGeometry.AlgebraicSpace S} →
      AlgebraicGeometry.AlgebraicSpace.IdealSubobject X → ℕ → Prop)
