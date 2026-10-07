module

public import ReasLib.AlgebraicGeometry.Scheme.Module.ArtinianPushforward
import StacksCheckRecall

@[expose] public section

open AlgebraicGeometry CategoryTheory CategoryTheory.ObjectProperty

universe u

namespace AlgebraicGeometry.Scheme.QCoh

/- Lemma 75.12.1. Let `S` be a Noetherian affine scheme. Every injective object of
`QCoh S` is a small filtered colimit of quasi-coherent sheaves of the form
`(Z_i ⟶ S)_* G_i`, where each `Z_i` is the spectrum of an Artinian ring and each
`G_i` is a coherent module on `Z_i`. -/
@[stacks 09TI]
#check
  (AlgebraicGeometry.Scheme.QCoh.injective_ind_artinianSpecCoherentPushforward :
    ∀ {S : Scheme.{u}} [IsAffine S] [IsNoetherian S] (J : QCoh S) [Injective J],
      (isArtinianSpecCoherentPushforward S).ind.{u} J)

end AlgebraicGeometry.Scheme.QCoh
