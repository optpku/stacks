/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import Mathlib.AlgebraicGeometry.Morphisms.Basic
public import ReasLib.CategoryTheory.MorphismProperty.Over
import StacksCheckRecall

@[expose] public section

open CategoryTheory Limits
open AlgebraicGeometry

universe u

namespace AlgebraicGeometry

section ObjectsOverBase

variable (P : Over.ObjectPropertyFamily Scheme.{u})
variable [P.IsStableUnderBaseChange]

/- Definition 26.18.3 (1): a base-indexed object property is stable under base change when
every pullback square preserves it. -/
@[stacks 01JZ] #check Over.ObjectPropertyFamily.IsStableUnderBaseChange
#check Over.ObjectPropertyFamily.IsStableUnderBaseChange.of_isPullback (P := P)
#check Over.ObjectPropertyFamily.IsStableUnderBaseChange.pullback (P := P)

end ObjectsOverBase

section MorphismsOverBase

variable (P : Over.MorphismPropertyFamily Scheme.{u})
variable [P.IsStableUnderBaseChange]

/- Definition 26.18.3 (2): a base-indexed slice-morphism property is stable under base change
when every induced map between pullback objects preserves it. -/
@[stacks 01JZ] #check Over.MorphismPropertyFamily.IsStableUnderBaseChange
#check Over.MorphismPropertyFamily.IsStableUnderBaseChange.of_isPullback (P := P)
#check Over.MorphismPropertyFamily.IsStableUnderBaseChange.pullbackMap (P := P)

end MorphismsOverBase

section GlobalPropertyBridge

variable (P : MorphismProperty Scheme.{u}) [P.IsStableUnderBaseChange]

#check P.overObjFamily
#check P.overFamily
#synth P.overObjFamily.IsStableUnderBaseChange
#synth P.overFamily.IsStableUnderBaseChange
#check MorphismProperty.isStableUnderBaseChange_iff_overObjFamily P
#check MorphismProperty.isStableUnderBaseChange_iff_overFamily P

end GlobalPropertyBridge

end AlgebraicGeometry
