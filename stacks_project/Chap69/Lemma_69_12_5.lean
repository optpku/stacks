module

public import stacks_project.Chap69.Lemma_69_12_5_Coherent
import StacksCheckRecall

@[expose] public section

open AlgebraicGeometry CategoryTheory
open CategoryTheory.MonoidalCategory
open AlgebraicGeometry.AlgebraicSpace
open AlgebraicGeometry.AlgebraicSpace.Modules

universe u

/- Lemma 69.12.5 (1): the tensor product of coherent modules on a locally Noetherian algebraic
space is coherent. -/
@[stacks 07UE] #check
  (@AlgebraicGeometry.AlgebraicSpace.Modules.isCoherent_tensor :
    ∀ {S : Scheme.{u}} {X : AlgebraicSpace S} [IsLocallyNoetherian X]
      {F G : X.Modules} [F.IsCoherent] [G.IsCoherent], (F ⊗ G).IsCoherent)

/- Lemma 69.12.5 (2): the internal Hom of coherent modules on a locally Noetherian algebraic
space is coherent. -/
@[stacks 07UE] #check
  (@AlgebraicGeometry.AlgebraicSpace.Modules.isCoherent_internalHom :
    ∀ {S : Scheme.{u}} {X : AlgebraicSpace S} [IsLocallyNoetherian X]
      {F G : X.Modules} [F.IsCoherent] [G.IsCoherent],
      (internalHom F G).IsCoherent)
