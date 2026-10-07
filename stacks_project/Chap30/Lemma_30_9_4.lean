module

import StacksCheckRecall
import ReasLib.AlgebraicGeometry.Scheme.Module.Coherent.InternalHom
import ReasLib.AlgebraicGeometry.Scheme.Module.Coherent.Tensor

@[expose] public section

open AlgebraicGeometry
open CategoryTheory
open CategoryTheory.MonoidalCategory
open CategoryTheory.MonoidalClosed

/- Lemma 30.9.4 (1): The tensor product of coherent modules on a locally Noetherian scheme is
coherent. -/
@[stacks 01Y2] #check
  (@AlgebraicGeometry.Scheme.Modules.isCoherent_tensor :
    ∀ {X : Scheme} {F G : X.Modules} [IsLocallyNoetherian X]
      [F.IsCoherent] [G.IsCoherent], (F ⊗ G).IsCoherent)

/- Lemma 30.9.4 (2): The internal Hom of coherent modules on a locally Noetherian scheme is
coherent. -/
@[stacks 01Y2] #check
  (@AlgebraicGeometry.Scheme.Modules.isCoherent_internalHom :
    ∀ {X : Scheme} {F G : X.Modules} [IsLocallyNoetherian X]
      [F.IsCoherent] [G.IsCoherent], ((ihom F).obj G).IsCoherent)
