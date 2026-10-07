module

public import stacks_project.Chap71.Definition_71_7_6_ZeroScheme
import StacksCheckRecall

@[expose] public section

open CategoryTheory CategoryTheory.MonoidalCategory AlgebraicGeometry
open AlgebraicGeometry.AlgebraicSpace

noncomputable section

universe u

/- Definition 71.7.6
Let `S` be a scheme. Let `X` be an algebraic space over `S`. Let `ℒ` be an invertible sheaf.
Let `s ∈ Γ(X, ℒ)`. The zero scheme of `s` is the closed subspace `Z(s) ⊂ X` defined by the
quasi-coherent sheaf of ideals `I ⊂ 𝒪_X` which is the image of the map
`s : ℒ^{⊗ -1} ⟶ 𝒪_X`.
-/
@[stacks 0845] #check
  (zeroScheme :
    {S : Scheme.{u}} → {X : AlgebraicSpace S} → (ℒ : X.Modules) →
      [isInvertibleObject ℒ] → ℒ.sections → ClosedSubspace X)
