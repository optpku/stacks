module

public import ReasLib.LinearAlgebra.ExteriorPower.RestrictScalars
import StacksCheckRecall

/-!
# Tensor comparison for Lemma 10.13.4

The reusable comparison is the arbitrary-family API in `PiTensorProduct`.
Its `RestrictScalars` codomain avoids installing module structures on the raw
tensor and exterior powers in this chapter.

@stack 0H1C
-/

@[stacks 0H1C "bundled tensor comparison after restriction of scalars"]
#check @PiTensorProduct.RestrictScalars.map

@[stacks 0H1C "bundled tensor comparison on pure tensors"]
#check @PiTensorProduct.RestrictScalars.map_tprod

@[stacks 0H1C "surjective bundled tensor comparison"]
#check @PiTensorProduct.RestrictScalars.map_surjective

@[stacks 0H1C "entrywise tensor comparison factorization"]
#check @PiTensorProduct.restrictScalarsMap_factor

@[stacks 0H1C "scalar-tower specialization"]
#check @PiTensorProduct.scalarTowerMap

@[stacks 0H1C "bundled tensor-to-exterior comparison factorization"]
#check @exteriorPower.RestrictScalars.quotient_factor

@[stacks 0H1C "bundled tensor-to-exterior comparison through the source exterior power"]
#check @exteriorPower.RestrictScalars.quotient_factor_exteriorPower
