module

public import stacks_project.Chap66.Lemma_66_16_7_OpenMap
import StacksCheckRecall

@[expose] public section

universe u

open CategoryTheory AlgebraicGeometry

/- Lemma 66.16.7: let `S` be a scheme. If `X ⟶ Y` is an étale morphism of algebraic spaces
over `S`, then the associated map `|X| → |Y|` of topological spaces is open. -/
@[stacks 03IR] #check
  (AlgebraicGeometry.AlgebraicSpace.Etale.isOpenMap :
    ∀ {S : Scheme.{u}} {X Y : AlgebraicSpace S} (f : X ⟶ Y) [AlgebraicSpace.Etale f],
      IsOpenMap (AlgebraicSpace.Points.map f))
