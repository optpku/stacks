module

public import ReasLib.Algebra.Category.ModuleCat.Sheaf.RingedSite.DifferentialGraded.MappingCone.Identity
import StacksCheckRecall

@[expose] public section

/-!
# Remark 24.22.5

The reusable identity-cone pair, compatibility, representing-morphism, and bijectivity APIs live
in the neutral `DifferentialGraded.MappingCone.Identity` support leaf.  This file is the
source-facing recall block for the remark.
-/

open SheafOfModules.RingedSite.DifferentialGradedModule.MappingCone

/- Remark 24.22.5: morphisms out of the identity cone are represented by compatible unit-section
   pairs in degrees `0` and `-1`. -/
#check @Identity.Pair
#check @Identity.Pair.Compatible
#check @Identity.CompatiblePair
#check @Identity.Pair.compatible_mk
#check @Identity.cone
#check @Identity.cone_X
#check @Identity.cone_d
#check @Identity.zeroUnit
#check @Identity.negOneUnit
#check @Identity.pair
#check @Identity.pair_compatible
#check @Identity.compatiblePair
#check @Identity.CompatiblePair.hom
#check @Identity.CompatiblePair.hom_f
#check @Identity.CompatiblePair.hom_spec
#check @Identity.CompatiblePair.hom_map
@[stacks 0FS8] #check @Identity.homEquiv
#check @Identity.Pair.existsUnique_hom_iff_compatible
#check @Identity.compatiblePair_bijective
