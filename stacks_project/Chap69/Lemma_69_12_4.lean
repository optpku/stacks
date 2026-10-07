module

public import stacks_project.Chap69.Lemma_69_12_4_Subquotient
import StacksCheckRecall

@[expose] public section

open AlgebraicGeometry CategoryTheory
open AlgebraicGeometry.AlgebraicSpace
open AlgebraicGeometry.AlgebraicSpace.Modules

universe u

/- Lemma 69.12.4 (1): on a locally Noetherian algebraic space over a scheme, every
quasi-coherent submodule of a coherent module is coherent. -/
@[stacks 07UD] #check
  (isCoherent_subobject_of_isQuasicoherent :
    ∀ {S : Scheme.{u}} {X : AlgebraicSpace S} [IsLocallyNoetherian X]
      (F : X.Modules) [F.IsCoherent] (G : Subobject F)
      [((G : X.Modules)).IsQuasicoherent],
      ((G : X.Modules)).IsCoherent)

/- Lemma 69.12.4 (2): on a locally Noetherian algebraic space over a scheme, every
quasi-coherent quotient of a coherent module is coherent. -/
@[stacks 07UD] #check
  (isCoherent_of_epi_from_coherent :
    ∀ {S : Scheme.{u}} {X : AlgebraicSpace S} [IsLocallyNoetherian X]
      {F G : X.Modules} [F.IsCoherent] [G.IsQuasicoherent]
      (π : F ⟶ G) [Epi π],
      G.IsCoherent)
