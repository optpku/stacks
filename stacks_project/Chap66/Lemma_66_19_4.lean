module

public import ReasLib.AlgebraicGeometry.AlgebraicSpace.GeometricPoint.Lift
import StacksCheckRecall

@[expose] public section

universe u

open CategoryTheory AlgebraicGeometry

/- Lemma 66.19.4: let `S` be a scheme. Let `X` be an algebraic space over `S`. Let
`xbar : Spec(k) ⟶ X` be a geometric point of `X` lying over `x ∈ |X|`. Let `φ : U ⟶ X`
be an étale morphism of algebraic spaces and let `u ∈ |U|` with `φ(u) = x`. Then there
exists a geometric point `ubar : Spec(k) ⟶ U` lying over `u` with `xbar = φ ∘ ubar`. -/
@[stacks 05VN] #check
  (AlgebraicGeometry.AlgebraicSpace.GeometricPoint.exists_lift_of_etale :
    ∀ {S : Scheme.{u}} {X U : AlgebraicSpace S}
      (xbar : AlgebraicSpace.GeometricPoint X) (x : AlgebraicSpace.Points X),
      xbar.liesOver x →
        ∀ (f : U ⟶ X) [AlgebraicSpace.Etale f] (u : AlgebraicSpace.Points U),
          AlgebraicSpace.Points.map f u = x →
            ∃ ubar : AlgebraicSpace.GeometricPoint U,
              ubar.liesOver u ∧ ubar.map f = xbar)
