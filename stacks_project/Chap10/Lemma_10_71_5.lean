module

public import ReasLib.Algebra.Homology.ChainComplex.FreeResolution.HomCohomology
import StacksCheckRecall

@[expose] public section

/-!
# Lemma 10.71.5

@stack 00LT
-/

@[stacks 00LT "(1), independence of the compatible lift"]
#check @ChainComplex.IsFreeResolution.homologyMap_eq_of_compatibleLifts

@[stacks 00LT "(2), isomorphism induced by a lifted isomorphism"]
#check @ChainComplex.IsFreeResolution.homologyMap_isIso_of_isIso

@[stacks 00LT "(3), identity induced by an identity lift"]
#check @ChainComplex.IsFreeResolution.homologyMap_eq_id

/- Reusable lift and induced-map objects behind the three source clauses. -/
#check @ChainComplex.IsFreeResolution.identityLift
#check @ChainComplex.IsFreeResolution.compLift
#check @ChainComplex.IsFreeResolution.inverseLift
#check @ChainComplex.IsFreeResolution.homologyMap
