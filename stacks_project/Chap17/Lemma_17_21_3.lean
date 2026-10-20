module

public import ReasLib.AlgebraicGeometry.RingedSpace.Module.AlgebraSheaf.Pullback
import StacksCheckRecall

@[expose] public section

open CategoryTheory
open AlgebraicGeometry
open scoped AlgebraicGeometry

/- Lemma 17.21.3 (01CI) (1): pullback commutes canonically with the tensor-algebra sheaf
construction. -/
@[stacks 01CI "(1), tensor algebra"]
#check (@RingedSpace.TensorAlg.Pullback.comparison_isIso :
  ∀ {X Y : RingedSpace} (f : X ⟶ Y) (F : Y.Modules),
    IsIso (RingedSpace.TensorAlg.Pullback.comparison f F))
#check @RingedSpace.TensorAlg.Pullback.comparisonInv
#check @RingedSpace.TensorAlg.Pullback.comparison_hom_inv_id
#check @RingedSpace.TensorAlg.Pullback.comparison_inv_hom_id
#check @RingedSpace.TensorAlg.Pullback.comparisonIso
#check @RingedSpace.TensorAlg.Pullback.comparisonIso_hom
#check @RingedSpace.TensorAlg.Pullback.comparisonIso_inv

/- The tensor comparisons form a natural transformation in the module sheaf. -/
#check @RingedSpace.TensorAlg.Pullback.natTrans
#check @RingedSpace.TensorAlg.Pullback.natTrans_isIso
#check @RingedSpace.TensorAlg.Pullback.comparisonNatIso
#check @RingedSpace.TensorAlg.Pullback.comparisonNatIso_app
#check @RingedSpace.TensorAlg.Pullback.invNatTrans
#check @RingedSpace.TensorAlg.Pullback.natTrans_hom_inv_id
#check @RingedSpace.TensorAlg.Pullback.natTrans_inv_hom_id
#check @RingedSpace.TensorAlg.Pullback.comparisonNatIso_hom
#check @RingedSpace.TensorAlg.Pullback.comparisonNatIso_inv_app
#check @RingedSpace.TensorAlg.Pullback.comparisonNatIso_inv

/- Naturality of the tensor comparison in the module sheaf. -/
#check @RingedSpace.TensorAlg.Pullback.comparison_naturality

/- The tensor comparison preserves the degree-one inclusion. -/
#check @RingedSpace.TensorAlg.Pullback.comparison_ι

/- The tensor comparison is compatible with the algebra unit and multiplication. -/
#check @RingedSpace.TensorAlg.Pullback.comparison_one
#check @RingedSpace.TensorAlg.Pullback.comparison_mul

/- Lemma 17.21.3 (01CI) (2): pullback commutes canonically with the exterior-algebra sheaf
construction. -/
@[stacks 01CI "(2), exterior algebra"]
#check (@RingedSpace.ExteriorAlg.Pullback.comparison_isIso :
  ∀ {X Y : RingedSpace} (f : X ⟶ Y) (F : Y.Modules),
    IsIso (RingedSpace.ExteriorAlg.Pullback.comparison f F))
#check @RingedSpace.ExteriorAlg.Pullback.comparisonInv
#check @RingedSpace.ExteriorAlg.Pullback.comparison_hom_inv_id
#check @RingedSpace.ExteriorAlg.Pullback.comparison_inv_hom_id
#check @RingedSpace.ExteriorAlg.Pullback.comparisonIso
#check @RingedSpace.ExteriorAlg.Pullback.comparisonIso_hom
#check @RingedSpace.ExteriorAlg.Pullback.comparisonIso_inv

/- The exterior comparisons form a natural transformation in the module sheaf. -/
#check @RingedSpace.ExteriorAlg.Pullback.natTrans
#check @RingedSpace.ExteriorAlg.Pullback.natTrans_isIso
#check @RingedSpace.ExteriorAlg.Pullback.comparisonNatIso
#check @RingedSpace.ExteriorAlg.Pullback.comparisonNatIso_app
#check @RingedSpace.ExteriorAlg.Pullback.invNatTrans
#check @RingedSpace.ExteriorAlg.Pullback.natTrans_hom_inv_id
#check @RingedSpace.ExteriorAlg.Pullback.natTrans_inv_hom_id
#check @RingedSpace.ExteriorAlg.Pullback.comparisonNatIso_hom
#check @RingedSpace.ExteriorAlg.Pullback.comparisonNatIso_inv_app
#check @RingedSpace.ExteriorAlg.Pullback.comparisonNatIso_inv

/- Naturality of the exterior comparison in the module sheaf. -/
#check @RingedSpace.ExteriorAlg.Pullback.comparison_naturality

/- The exterior comparison preserves the degree-one inclusion. -/
#check @RingedSpace.ExteriorAlg.Pullback.comparison_ι

/- The exterior comparison is compatible with the algebra unit and multiplication. -/
#check @RingedSpace.ExteriorAlg.Pullback.comparison_one
#check @RingedSpace.ExteriorAlg.Pullback.comparison_mul

/- Lemma 17.21.3 (01CI) (3): pullback commutes canonically with the symmetric-algebra sheaf
construction. -/
@[stacks 01CI "(3), symmetric algebra"]
#check (@RingedSpace.SymmetricAlg.Pullback.comparison_isIso :
  ∀ {X Y : RingedSpace} (f : X ⟶ Y) (F : Y.Modules),
    IsIso (RingedSpace.SymmetricAlg.Pullback.comparison f F))
#check @RingedSpace.SymmetricAlg.Pullback.comparisonInv
#check @RingedSpace.SymmetricAlg.Pullback.comparison_hom_inv_id
#check @RingedSpace.SymmetricAlg.Pullback.comparison_inv_hom_id
#check @RingedSpace.SymmetricAlg.Pullback.comparisonIso
#check @RingedSpace.SymmetricAlg.Pullback.comparisonIso_hom
#check @RingedSpace.SymmetricAlg.Pullback.comparisonIso_inv

/- The symmetric comparisons form a natural transformation in the module sheaf. -/
#check @RingedSpace.SymmetricAlg.Pullback.natTrans
#check @RingedSpace.SymmetricAlg.Pullback.natTrans_isIso
#check @RingedSpace.SymmetricAlg.Pullback.comparisonNatIso
#check @RingedSpace.SymmetricAlg.Pullback.comparisonNatIso_app
#check @RingedSpace.SymmetricAlg.Pullback.invNatTrans
#check @RingedSpace.SymmetricAlg.Pullback.natTrans_hom_inv_id
#check @RingedSpace.SymmetricAlg.Pullback.natTrans_inv_hom_id
#check @RingedSpace.SymmetricAlg.Pullback.comparisonNatIso_hom
#check @RingedSpace.SymmetricAlg.Pullback.comparisonNatIso_inv_app
#check @RingedSpace.SymmetricAlg.Pullback.comparisonNatIso_inv

/- Naturality of the symmetric comparison in the module sheaf. -/
#check @RingedSpace.SymmetricAlg.Pullback.comparison_naturality

/- The symmetric comparison preserves the degree-one inclusion. -/
#check @RingedSpace.SymmetricAlg.Pullback.comparison_ι

/- The symmetric comparison is compatible with the algebra unit and multiplication. -/
#check @RingedSpace.SymmetricAlg.Pullback.comparison_one
#check @RingedSpace.SymmetricAlg.Pullback.comparison_mul
