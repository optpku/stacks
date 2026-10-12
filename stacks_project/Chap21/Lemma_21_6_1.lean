/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import ReasLib.Algebra.Category.ModuleCat.Sheaf.Picard.Cohomology
import StacksCheckRecall

@[expose] public section

/- Lemma 21.6.1 (040E): the canonical isomorphism between the Picard group and the first
cohomology of the units sheaf is represented by an explicit additive homomorphism and its
bijectivity theorem. -/
@[stacks 040E]
#check @SheafOfModules.RingedSite.PicardGroup.cohomologyClass

#check @SheafOfModules.RingedSite.PicardGroup.cohomologyClass_apply
#check @SheafOfModules.RingedSite.PicardGroup.cohomologyClass_bijective
#check @SheafOfModules.RingedSite.PicardGroup.localGeneratorTorsor
#check @CategoryTheory.Sheaf.Torsor.Cohomology.classMap
