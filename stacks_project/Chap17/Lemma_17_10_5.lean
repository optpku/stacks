module

public import ReasLib.AlgebraicGeometry.RingedSpace.Module.Associated
import StacksCheckRecall

/-!
# Modules associated to modules over global scalars

The reusable construction and all six clauses of Lemma 17.10.5 are owned by
`RingedSpace.Module.Associated`; this chapter file is a source correspondence only.
-/

@[expose] public section

namespace AlgebraicGeometry

open RingedSpace.Module

/- Lemma 17.10.5 (01BH) (1): a cokernel of free module sheaves obtained from a free presentation
of `M` is canonically isomorphic to the module sheaf associated to `M`. -/
@[stacks 01BH "(1)"]
#check @Associated.Presentation.iso

#check @Associated.freeNatIso
#check @Associated.freeNatTrans
#check @Associated.freeNatTransInv
#check @Associated.freeNatTrans_hom_inv_id
#check @Associated.freeNatTrans_inv_hom_id
#check @Associated.freeNatIso_hom
#check @Associated.freeNatIso_inv
#check @Associated.freeNatIso_hom_app
#check @Associated.freeNatIso_inv_app

#check @Associated.Presentation.homEquiv

/- Lemma 17.10.5 (01BH) (2): the sheafification of `U ↦ O_X(U) ⊗_R M` is canonically isomorphic
to the module sheaf associated to `M`. -/
@[stacks 01BH "(2)"]
#check @Associated.fromPresheafIso

#check @Associated.fromPresheafComparisonInv

#check @Associated.associatedIso

/- Lemma 17.10.5 (01BH) (3): an associated module sheaf is quasi-coherent. -/
@[stacks 01BH "(3)"]
#check @Associated.obj_isQuasicoherent

/- Lemma 17.10.5 (01BH) (4): associated modules form a functor to quasi-coherent module sheaves
which preserves arbitrary colimits. -/
@[stacks 01BH "(4)"]
#check @Associated.qcFunctor_preservesColimits

/- Lemma 17.10.5 (01BH) (5): the stalk of an associated module sheaf is naturally extension of
scalars to the local ring. -/
@[stacks 01BH "(5)"]
#check @Associated.stalkFunctorIso

#check @Associated.pointStalkMap
#check @Associated.pointStalkMap_comp
#check @Associated.stalkComparison
#check @Associated.stalkComparisonInv
#check @Associated.stalkComparison_hom_inv_id
#check @Associated.stalkComparison_inv_hom_id
#check @Associated.stalkComparisonIso
#check @Associated.stalkComparisonIso_hom
#check @Associated.stalkComparisonIso_inv
#check @Associated.stalkComparisonInv_naturality
#check @Associated.stalkFunctorNatTrans
#check @Associated.stalkFunctorInvNatTrans
#check @Associated.stalkFunctorNatTrans_hom_inv_id
#check @Associated.stalkFunctorNatTrans_inv_hom_id
#check @Associated.stalkFunctorIso_hom
#check @Associated.stalkFunctorIso_inv
#check @Associated.stalkFunctorIso_hom_app
#check @Associated.stalkFunctorIso_inv_app
#check @AlgebraicGeometry.RingedPoint.Module.stalkComparisonInv
#check @AlgebraicGeometry.RingedPoint.Module.stalkComparison_hom_inv_id
#check @AlgebraicGeometry.RingedPoint.Module.stalkComparison_inv_hom_id
#check @AlgebraicGeometry.RingedPoint.Module.stalkModuleIso
#check @AlgebraicGeometry.RingedPoint.Module.stalkModuleIso_hom
#check @AlgebraicGeometry.RingedPoint.Module.stalkModuleIso_inv
#check @AlgebraicGeometry.RingedPoint.Module.stalkFunctorNatTrans
#check @AlgebraicGeometry.RingedPoint.Module.stalkFunctorInvNatTrans
#check @AlgebraicGeometry.RingedPoint.Module.stalkFunctorNatTrans_hom_inv_id
#check @AlgebraicGeometry.RingedPoint.Module.stalkFunctorNatTrans_inv_hom_id
#check @AlgebraicGeometry.RingedPoint.Module.stalkFunctorIso
#check @AlgebraicGeometry.RingedPoint.Module.stalkFunctorIso_hom
#check @AlgebraicGeometry.RingedPoint.Module.stalkFunctorIso_inv
#check @AlgebraicGeometry.RingedPoint.Module.stalkFunctorIso_hom_app
#check @AlgebraicGeometry.RingedPoint.Module.stalkFunctorIso_inv_app
#check @AlgebraicGeometry.RingedSpace.Hom.pullbackStalkComparison
#check @AlgebraicGeometry.RingedSpace.Hom.pullbackStalkComparison_hom_inv_id
#check @AlgebraicGeometry.RingedSpace.Hom.pullbackStalkComparison_inv_hom_id
#check @AlgebraicGeometry.RingedSpace.Hom.pullbackStalkIso
#check @AlgebraicGeometry.RingedSpace.Hom.pullbackStalkIso_hom
#check @AlgebraicGeometry.RingedSpace.Hom.pullbackStalkIso_inv
#check @AlgebraicGeometry.RingedSpace.Hom.pullbackStalkComparisonInv

/- Lemma 17.10.5 (01BH) (6): the associated-module functor is left adjoint to global sections
with scalars restricted along `R → Γ(X, O_X)`. -/
@[stacks 01BH "(6)"]
#check @Associated.adjunction
#check @Associated.geometricSectionsIsoApp
#check @Associated.geometricSectionsNatTrans
#check @Associated.geometricSectionsInvNatTrans
#check @Associated.geometricSectionsNatTrans_hom_inv_id
#check @Associated.geometricSectionsNatTrans_inv_hom_id
#check @Associated.geometricSectionsIso
#check @Associated.geometricSectionsIso_hom
#check @Associated.geometricSectionsIso_inv
#check @Associated.geometricSectionsIso_hom_app
#check @Associated.geometricSectionsIso_inv_app

end AlgebraicGeometry
