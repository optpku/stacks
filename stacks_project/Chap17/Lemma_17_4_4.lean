/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import ReasLib.Algebra.Category.ModuleCat.Sheaf.GeneratedSubobject
import StacksCheckRecall

@[expose] public section

/- Lemma 17.4.4: an indexed family of local sections has a unique smallest containing
module-sheaf subobject. -/
@[stacks 01AP]
#check @SheafOfModules.Subobject.existsUnique_generatedBySections

/- Containment is equivalently expressed by lifting each section through the subobject
inclusion. -/
#check @SheafOfModules.Subobject.containsSections_iff

/- The canonical generated subobject realizes the least element in Lemma 17.4.4. -/
#check @SheafOfModules.Subobject.generatedBySections_isLeast

/- The least-subobject property is exposed in the rewrite-oriented form used downstream. -/
#check @SheafOfModules.Subobject.generatedBySections_le_iff
