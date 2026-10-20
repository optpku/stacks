module

public import ReasLib.AlgebraicGeometry.AlgebraicSpace.Module.SchemeTheoreticSupport.Coherent
import StacksCheckRecall

@[expose] public section

open AlgebraicGeometry CategoryTheory
open AlgebraicGeometry.AlgebraicSpace
open AlgebraicGeometry.AlgebraicSpace.Modules

universe u

/- Lemma 69.12.7: Let `S` be a scheme. Let `X` be a locally Noetherian algebraic space over
`S`. Let `F` be a coherent `𝒪_X`-module. Let `i : Z ⟶ X` be a scheme-theoretic support of
`F` and `G` a quasi-coherent `𝒪_Z`-module such that `(pushforward i).obj G ≅ F`. Then `G`
is a coherent `𝒪_Z`-module. -/
@[stacks 07UG]
#check (AlgebraicGeometry.AlgebraicSpace.Modules.isCoherent_of_pushforward_iso :
  ∀ {S : Scheme.{u}} {X Z : AlgebraicSpace S} [IsLocallyNoetherian X]
    (F : X.Modules) [F.IsCoherent] (i : Z ⟶ X) [IsSchemeTheoreticSupport F i]
    (G : Z.Modules) [G.IsQuasicoherent] (_ : (pushforward i).obj G ≅ F),
    G.IsCoherent)
