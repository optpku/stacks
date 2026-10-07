module

import ReasLib.AlgebraicGeometry.Scheme.CoherentFormalModule.Pullback
import StacksCheckRecall

@[expose] public section

open AlgebraicGeometry
open CategoryTheory
open Opposite

noncomputable section

universe u

namespace AlgebraicGeometry.Scheme

/- Lemma 30.23.10: let `f : X' ⟶ X` be a morphism of Noetherian schemes, let
`I : X.IdealSheafData` define a closed subscheme `Z ⊆ X`, and let `I.comap f` define the
scheme-theoretic inverse image `Z' = f^{-1} Z`. If `f` is flat and the induced morphism
`Z' ⟶ Z` is an isomorphism, then the pullback functor
`f^* : Coh(X, I) ⥤ Coh(X', I.comap f)` from Lemma 30.23.9 is an equivalence. -/
@[stacks 0EHQ] #check
  (AlgebraicGeometry.Scheme.CoherentFormalModules.pullback_isEquivalence :
    ∀ {X X' : Scheme.{u}} [IsNoetherian X] [IsNoetherian X']
      (f : X' ⟶ X) [Flat f] (I : X.IdealSheafData)
      [IsIso (IdealSheafData.subschemeMap (I.comap f) I f (I.le_map_comap f))]
      (reindex : CoherentFormalModules X I ⥤ CoherentFormalModules X' (I.comap f))
      (hF : IsCoherentFormalModulesPullbackFunctor f I reindex),
      Functor.IsEquivalence reindex)

end AlgebraicGeometry.Scheme
