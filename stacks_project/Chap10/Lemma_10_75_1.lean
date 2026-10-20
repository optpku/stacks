module

public import ReasLib.Algebra.Homology.ChainComplex.FreeResolution.TensorHomology
import StacksCheckRecall

@[expose] public section

/-!
# Lemma 10.75.1

@stack 00LZ
-/

@[stacks 00LZ "(1), independence of the compatible lift after tensoring"]
#check @ChainComplex.IsFreeResolution.tensorHomologyMap_eq_of_compatibleLifts

@[stacks 00LZ "(2), tensor-homology isomorphism induced by a lifted isomorphism"]
#check @ChainComplex.IsFreeResolution.tensorHomologyMap_isIso_of_isIso

@[stacks 00LZ "(3), identity induced by an identity lift after tensoring"]
#check @ChainComplex.IsFreeResolution.tensorHomologyMap_eq_id

#check @ChainComplex.IsFreeResolution.tensorComplexMap
#check @ChainComplex.IsFreeResolution.tensorHomologyMap
