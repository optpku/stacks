module

public import ReasLib.AlgebraicGeometry.RingedSite.Cotangent.Functoriality
import StacksCheckRecall

@[expose] public section

open CategoryTheory

universe u

/- 92.6.0.2: the double square of ringed topoi induced by a commutative square of rings,
with coefficient-change maps, polynomial base change, projections to the ringed point,
and the lower-right identity. -/
@[stacks 08QN] #check (RingedSite.Cotangent.Functoriality.ofCommSq :
  ∀ {A A' B B' : CommRingCat.{u}} {α : A ⟶ B} {ρ : A ⟶ A'}
    {β : A' ⟶ B'} {φ : B ⟶ B'},
    CommSq ρ α β φ → RingedSite.Cotangent.Functoriality.Diagram (α := α) (β := β))
