/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import ReasLib.Algebra.Category.ModuleCat.Sheaf.Localization.Compact
import StacksCheckRecall

@[expose] public section

/- Lemma 18.30.4: for quasi-compact `U`, the localized structure module `j_{U!}R_U` is compact;
equivalently, its represented additive Hom functor preserves arbitrary direct sums. -/
@[stacks 0936]
#check @CategoryTheory.Coverage.QuasiCompactObject.structureModuleIsCompact

/- Sieve-saturated specializations are directly available in generic and ringed-site notation. -/
#check @SheafOfModules.RingedSite.LocalizedStructureModuleExtensionByZero.isCompactObject
#check @SheafOfModules.Localization.structureModule_isCompactObject
