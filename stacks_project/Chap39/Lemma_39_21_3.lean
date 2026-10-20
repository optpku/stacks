module

public import ReasLib.AlgebraicGeometry.GroupoidScheme.Cartesian.Descent
import StacksCheckRecall

@[expose] public section

open CategoryTheory

universe u

/- Lemma 39.21.3: Let `S` be a scheme and `f : X ⟶ Y` a morphism of schemes over `S`.
The category of groupoid schemes cartesian over the Čech groupoid
`pullback (discrete Y) f` is equivalent to the category of descent data relative to
`X/Y`. -/
@[stacks 0APF] #check
  (AlgebraicGeometry.GroupoidScheme.CartesianOver.descentEquivalence :
    {S : AlgebraicGeometry.Scheme.{u}} → {X Y : Over S} → (f : X ⟶ Y) →
      AlgebraicGeometry.GroupoidScheme.CartesianOver
          (AlgebraicGeometry.GroupoidScheme.pullback
            (AlgebraicGeometry.GroupoidScheme.discrete Y) f) ≌
        AlgebraicGeometry.Scheme.DescentData
          (fun _ : PUnit.{1} ↦ X.left) (fun _ : PUnit.{1} ↦ f.left))
