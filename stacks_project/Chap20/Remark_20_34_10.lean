module

public import ReasLib.AlgebraicGeometry.RingedSpace.Module.ClosedSubset.Derived.GlobalSections.CupProduct
public import ReasLib.CategoryTheory.Adjunction.RelativeCupProduct
import StacksCheckRecall

@[expose] public section

open CategoryTheory
open CategoryTheory.DerivedCategory
open AlgebraicGeometry
open AlgebraicGeometry.RingedSpace.ClosedSubset.GlobalSectionsWithSupport
open scoped RingedSpaceTensor
open scoped RingedSpaceDerivedGlobalSections
open scoped RingedSpaceClosedSupport

/-
Remark 20.34.10.  The reusable interface is owned by
`SupportedCupProduct` in ReasLib.  Its natural-transformation fields keep the supported, ambient,
and ordinary cup products concrete; `realizes` and `forget_comm` are the two compatibility laws.
The object-level `CupProductModel` is only the fixed-object bridge.  `ofAmbient` is the preferred
constructor when a geometric producer supplies the ambient map, while `ofMaps` remains the direct
constructor when the supported map is already available.  Downstream statements should consume
the family (or its `model` projection) rather than rebuild arrows or local instances.
-/
@[stacks 0G76 "Remark 20.34.10 supported cup product"]
#check @SupportedCupProduct

#check @SupportedCupProduct.ofMaps
#check @SupportedCupProduct.ofAmbient
#check @SupportedCupProduct.ofAmbient_map
#check @SupportedCupProduct.map
#check @SupportedCupProduct.ambientMap
#check @SupportedCupProduct.globalMap
#check @SupportedCupProduct.realizes
#check @SupportedCupProduct.forget_comm
#check @SupportedCupProduct.realizes_app
#check @SupportedCupProduct.model
#check @SupportedCupProduct.forget_spec
#check @SupportedCupProduct.derivedCommSq
#check @CupProductModel
#check @CupProductModel.ofMaps
#check @CupProductModel.ofAmbient
#check @CupProductModel.ofAmbient_map
#check @CupProductModel.map
#check @CupProductModel.realizes
#check @forgetCommSq
#check @map_commSq_of_forget
#check @SupportedCupProduct.cohomologyCommSq

/- The model-side map in the source is the generic right-adjoint tensor map; the concrete
adjunction, tensor functors, and comparison family are supplied by the surrounding setup. -/
#check @CategoryTheory.Adjunction.rightAdjointTensorMapOf
#check @CategoryTheory.Adjunction.relativeDerivedCupProduct
#check @CategoryTheory.Adjunction.relativeDerivedCupProduct_spec
