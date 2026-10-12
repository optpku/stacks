/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import ReasLib.AlgebraicGeometry.RingedSpace.Module.AlgebraSheaf.Stalk
import StacksCheckRecall

@[expose] public section

open AlgebraicGeometry

/- Lemma 17.21.2 (01CH), tensor case: the stalk of the tensor-algebra sheaf is canonically
isomorphic to the tensor algebra of the stalk module. -/
@[stacks 01CH "tensor algebra"]
#check @RingedSpace.TensorAlg.Stalk.comparison_isIso

/- The canonical isomorphism and both comparison maps are available explicitly. -/
#check @RingedSpace.TensorAlg.Stalk.comparisonIso
#check @RingedSpace.TensorAlg.Stalk.comparison
#check @RingedSpace.TensorAlg.Stalk.comparisonInv
#check @RingedSpace.TensorAlg.Stalk.comparisonIso_inv

/- The tensor-algebra comparisons assemble into a natural isomorphism, whose forward map is the
previous pointwise invertible natural transformation. -/
#check @RingedSpace.TensorAlg.Stalk.comparisonNatIso
#check @RingedSpace.TensorAlg.Stalk.natTrans
#check @RingedSpace.TensorAlg.Stalk.invNatTrans
#check @RingedSpace.TensorAlg.Stalk.natTrans_hom_inv_id
#check @RingedSpace.TensorAlg.Stalk.natTrans_inv_hom_id
#check @RingedSpace.TensorAlg.Stalk.comparisonNatIso_hom
#check @RingedSpace.TensorAlg.Stalk.comparisonNatIso_inv
#check @RingedSpace.TensorAlg.Stalk.comparisonNatIso_hom_app
#check @RingedSpace.TensorAlg.Stalk.comparisonNatIso_inv_app
#check @RingedSpace.TensorAlg.Stalk.natTrans_isIso

/- Both tensor-algebra comparisons are characterized on germs of degree-one generators. -/
#check @RingedSpace.TensorAlg.Stalk.comparison_germ_ι
#check @RingedSpace.TensorAlg.Stalk.comparisonInv_germ_ι

/- The tensor-algebra comparison respects its degree-one inclusion, unit, and multiplication. -/
#check @RingedSpace.TensorAlg.Stalk.comparison_ι
#check @RingedSpace.TensorAlg.Stalk.comparisonInv_ι
#check @RingedSpace.TensorAlg.Stalk.comparison_one
#check @RingedSpace.TensorAlg.Stalk.comparison_mul

/- Both tensor-algebra comparisons are natural in the module sheaf. -/
#check @RingedSpace.TensorAlg.Stalk.comparison_naturality
#check @RingedSpace.TensorAlg.Stalk.comparisonInv_naturality

/- Lemma 17.21.2 (01CH), symmetric case: the stalk of the symmetric-algebra sheaf is
canonically isomorphic to the symmetric algebra of the stalk module. -/
@[stacks 01CH "symmetric algebra"]
#check @RingedSpace.SymmetricAlg.Stalk.comparison_isIso

/- The canonical isomorphism and both comparison maps are available explicitly. -/
#check @RingedSpace.SymmetricAlg.Stalk.comparisonIso
#check @RingedSpace.SymmetricAlg.Stalk.comparison
#check @RingedSpace.SymmetricAlg.Stalk.comparisonInv
#check @RingedSpace.SymmetricAlg.Stalk.comparisonIso_inv

/- The symmetric-algebra comparisons assemble into a natural isomorphism, whose forward map is
the previous pointwise invertible natural transformation. -/
#check @RingedSpace.SymmetricAlg.Stalk.comparisonNatIso
#check @RingedSpace.SymmetricAlg.Stalk.natTrans
#check @RingedSpace.SymmetricAlg.Stalk.invNatTrans
#check @RingedSpace.SymmetricAlg.Stalk.natTrans_hom_inv_id
#check @RingedSpace.SymmetricAlg.Stalk.natTrans_inv_hom_id
#check @RingedSpace.SymmetricAlg.Stalk.comparisonNatIso_hom
#check @RingedSpace.SymmetricAlg.Stalk.comparisonNatIso_inv
#check @RingedSpace.SymmetricAlg.Stalk.comparisonNatIso_hom_app
#check @RingedSpace.SymmetricAlg.Stalk.comparisonNatIso_inv_app
#check @RingedSpace.SymmetricAlg.Stalk.natTrans_isIso

/- Both symmetric-algebra comparisons are characterized on germs of degree-one generators. -/
#check @RingedSpace.SymmetricAlg.Stalk.comparison_germ_ι
#check @RingedSpace.SymmetricAlg.Stalk.comparisonInv_germ_ι

/- The symmetric-algebra comparison respects its degree-one inclusion, unit, and
multiplication. -/
#check @RingedSpace.SymmetricAlg.Stalk.comparison_ι
#check @RingedSpace.SymmetricAlg.Stalk.comparisonInv_ι
#check @RingedSpace.SymmetricAlg.Stalk.comparison_one
#check @RingedSpace.SymmetricAlg.Stalk.comparison_mul

/- Both symmetric-algebra comparisons are natural in the module sheaf. -/
#check @RingedSpace.SymmetricAlg.Stalk.comparison_naturality
#check @RingedSpace.SymmetricAlg.Stalk.comparisonInv_naturality

/- Lemma 17.21.2 (01CH), exterior case: the stalk of the exterior-algebra sheaf is canonically
isomorphic to the exterior algebra of the stalk module. -/
@[stacks 01CH "exterior algebra"]
#check @RingedSpace.ExteriorAlg.Stalk.comparison_isIso

/- The canonical isomorphism and both comparison maps are available explicitly. -/
#check @RingedSpace.ExteriorAlg.Stalk.comparisonIso
#check @RingedSpace.ExteriorAlg.Stalk.comparison
#check @RingedSpace.ExteriorAlg.Stalk.comparisonInv
#check @RingedSpace.ExteriorAlg.Stalk.comparisonIso_inv

/- The exterior-algebra comparisons assemble into a natural isomorphism, whose forward map is
the previous pointwise invertible natural transformation. -/
#check @RingedSpace.ExteriorAlg.Stalk.comparisonNatIso
#check @RingedSpace.ExteriorAlg.Stalk.natTrans
#check @RingedSpace.ExteriorAlg.Stalk.invNatTrans
#check @RingedSpace.ExteriorAlg.Stalk.natTrans_hom_inv_id
#check @RingedSpace.ExteriorAlg.Stalk.natTrans_inv_hom_id
#check @RingedSpace.ExteriorAlg.Stalk.comparisonNatIso_hom
#check @RingedSpace.ExteriorAlg.Stalk.comparisonNatIso_inv
#check @RingedSpace.ExteriorAlg.Stalk.comparisonNatIso_hom_app
#check @RingedSpace.ExteriorAlg.Stalk.comparisonNatIso_inv_app
#check @RingedSpace.ExteriorAlg.Stalk.natTrans_isIso

/- Both exterior-algebra comparisons are characterized on germs of degree-one generators. -/
#check @RingedSpace.ExteriorAlg.Stalk.comparison_germ_ι
#check @RingedSpace.ExteriorAlg.Stalk.comparisonInv_germ_ι

/- The exterior-algebra comparison respects its degree-one inclusion, unit, and
multiplication. -/
#check @RingedSpace.ExteriorAlg.Stalk.comparison_ι
#check @RingedSpace.ExteriorAlg.Stalk.comparisonInv_ι
#check @RingedSpace.ExteriorAlg.Stalk.comparison_one
#check @RingedSpace.ExteriorAlg.Stalk.comparison_mul

/- Both exterior-algebra comparisons are natural in the module sheaf. -/
#check @RingedSpace.ExteriorAlg.Stalk.comparison_naturality
#check @RingedSpace.ExteriorAlg.Stalk.comparisonInv_naturality
