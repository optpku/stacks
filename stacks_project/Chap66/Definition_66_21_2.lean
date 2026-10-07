module

public import stacks_project.Chap66.Definition_66_29_1_RingedSite
import StacksCheckRecall

@[expose] public section

universe u

open CategoryTheory Opposite AlgebraicGeometry AlgebraicGeometry.AlgebraicSpace

/- Definition 66.21.2: let `S` be a scheme and let `X` be an algebraic space over `S`.
The structure sheaf of `X` is the sheaf of rings `𝒪_X` on the small étale site
`X_étale` described in Lemma 66.21.1, i.e. `structureSheaf X` on
`smallEtaleTopology X`. -/
@[stacks 03G7] #check
  (AlgebraicGeometry.AlgebraicSpace.structureSheaf :
    ∀ {S : Scheme.{u}} (X : AlgebraicSpace S),
      Sheaf (smallEtaleTopology X) RingCat.{u})

#check (AlgebraicGeometry.AlgebraicSpace.structureSheaf_obj :
  ∀ {S : Scheme.{u}} {X : AlgebraicSpace S} (U : smallEtaleSite X),
    (structureSheaf X).obj.obj (op U) = RingCat.of Γ(U.left.left, ⊤))
