module

public import ReasLib.AlgebraicGeometry.RingedSite.Module.Derived.Compact.Generators
import StacksCheckRecall

@[expose] public section

#check @RingedSite.ModuleCat.quasiCompactGenerators
#check @RingedSite.ModuleCat.QuasiCompactGenerators.mem_iff
#check @RingedSite.ModuleCat.QuasiCompactGenerators.structureModule_mem
#check @RingedSite.ModuleCat.QuasiCompactGenerators.isCompactObject
#check @RingedSite.ModuleCat.QuasiCompactGenerators.isSeparating

/- Lemma 21.52.2 (094C): quasi-compact localized structure modules give bounded-complex
representatives, up to retract, for compact objects of the ringed-site derived category. -/
@[stacks 094C]
#check @RingedSite.ModuleCat.QuasiCompactGenerators.exists_retract_bounded
