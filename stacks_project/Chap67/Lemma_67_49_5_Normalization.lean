module

public import ReasLib.AlgebraicGeometry.AlgebraicSpace.Normalization.Absolute

/-!
Compatibility surface for the absolute-normalization construction.  The
mathematical declarations are owned by the reusable ReasLib modules; this
source-side module keeps the historical names available to chapter imports.
-/

@[expose] public section

open AlgebraicGeometry AlgebraicGeometry.Scheme

namespace AlgebraicGeometry.AlgebraicSpace

export AlgebraicGeometry.Scheme.Normalization
  (overNormalization overNormalizationTo overNormalization_left
   mapsTo_genericPoints_of_etale mapsTo_genericPoints_normalizationTo_comp
   genericPointSpectrumCoproductMap genericPointSpectrumCoproductMap_eq
   genericPointSpectrumCoproductMap_comp overNormalizationToPullback_lift_comm
   overNormalizationToPullback_lift_snd overNormalizationToPullback_left
   overNormalizationMap_left overNormalizationMap_w overNormalizationMap
   overNormalizationMap_comp existsUnique_overNormalizationMap_of_mapsTo)

export AlgebraicGeometry.Scheme.FppfSheafification
  (PresentedAlgebra presentedRing presentedRing_eq presentedSpec presentedSpec_eq
   presentedRingHomFromGamma presentedToGamma presentedHom presentedHom_eq
   presentedOver presentedOverHom presentedRingHom presentedSpecMap
   presentedOverMap FppfMatching plusTypeU plusTypeU_obj plusTypeUMap
   toPlusTypeU plusTypeULift sheafifyTypeU sheafifyTypeU_obj
   sheafifyTypeU_isSheaf toSheafifyTypeU toSheafifyTypeU_eq
   sheafifyTypeULift sheafifyTypeULift_eq sheafifyTypeULift_spec)

export AlgebraicGeometry.Scheme.PreRelation
  (quotientPresheafDescTo_respects quotientPresheafDescTo
   quotientPresheafDescTo_naturality quotientPresheafDescTo_mk)

/- The normalization map remains a real typed compatibility check for chapter users. -/
#check (normalizationTo : ∀ {S : Scheme} (X : AlgebraicSpace S)
  [HasFiniteIrreducibleComponentsOnCompactOpens X], X.normalization ⟶ X)

namespace PresentedAlgebra
export AlgebraicGeometry.Scheme.FppfSheafification.PresentedAlgebra (trivial map)
end PresentedAlgebra

namespace FppfMatching
export AlgebraicGeometry.Scheme.FppfSheafification.FppfMatching
  (restrictPieces mem_restrictPieces restrictIsAffine restrictPiece restrictPiece_mem
   restrictLE restrictPiece_map restrictVal restrict trivialPieces trivialPieces_isAffine
   ofSection Agree agree_restrict mapNat agree_mapNat arrow amalgamate amalgamate_agree)
end FppfMatching

end AlgebraicGeometry.AlgebraicSpace
