/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import ReasLib.CategoryTheory.Fibered.LowerShriek.DerivedComparison
import StacksCheckRecall

@[expose] public section

open CategoryTheory

namespace CategoryTheory.FiberedCategoryOver

/- Remark 21.38.7 (08PD): a morphism `t : F' ⟶ g⁻¹.obj F` induces a degree-zero
inverse-image map, whose adjoint transpose and the canonical composition isomorphism for
projection lower shriek give `Lπ'_!.obj (single.obj F') ⟶ Lπ_!.obj (single.obj F)`. -/
@[stacks 08PD "derived projection lower-shriek composition"]
#check @DerivedLowerShriek.projectionLowerShriekCompIso

@[stacks 08PD "degree-zero derived lower-shriek comparison"]
#check @DerivedLowerShriek.lowerShriekSingleComparison

@[stacks 08PD]
#check @DerivedLowerShriek.comparisonMap

end CategoryTheory.FiberedCategoryOver
