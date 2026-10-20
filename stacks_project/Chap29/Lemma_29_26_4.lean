module

import StacksCheckRecall
public import ReasLib.AlgebraicGeometry.Scheme.Module.FiniteLocallyFree.Generalization

open AlgebraicGeometry

universe u

/- Lemma 29.26.4: every finite flat quasi-coherent module is finite locally free if and only if
every closed subset stable under generalization is open. -/
@[stacks 053N] #check
  (AlgebraicGeometry.Scheme.Modules.finiteFlat_finiteLocallyFree_iff_closed_stableUnderGeneralization_isOpen :
    ∀ (X : Scheme.{u}),
      (∀ (ℱ : X.Modules) [ℱ.IsQuasicoherent] [ℱ.IsFiniteType] [ℱ.IsFlat],
        ℱ.IsFiniteLocallyFree) ↔
        ∀ Z : Set X, IsClosed Z → StableUnderGeneralization Z → IsOpen Z)
