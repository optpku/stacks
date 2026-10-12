/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import ReasLib.AlgebraicTopology.SimplicialObject.Truncated.Coskeleton.Existence
import StacksCheckRecall

/-!
@stack 09VS

# Remark 14.19.11 compatibility facade

The reusable existence instances are owned by ReasLib: binary products suffice in degree zero,
while finite connected limits suffice at every nonzero truncation level.
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits
open CategoryTheory.SimplicialObject

universe v u

noncomputable section

namespace CategoryTheory

variable {C : Type u} [Category.{v} C]

section Zero

variable [HasBinaryProducts C]

/- Remark 14.19.11 (1): binary products suffice for the existence of `cosk₀`. -/
@[stacks 09VS "Remark 14.19.11 (1)"]
#check (inferInstance :
  (truncation 0 : SimplicialObject C ⥤ SimplicialObject.Truncated C 0).IsLeftAdjoint)

end Zero

section Positive

variable (k : ℕ) [NeZero k] [HasFiniteConnectedLimits C]
variable (F : (SimplexCategory.Truncated k)ᵒᵖ ⥤ C)

/- Remark 14.19.11 (2): for nonzero `k`, finite connected limits supply the pointwise right Kan
extensions defining the canonical functor `Truncated.cosk k`. -/
@[stacks 09VS "Remark 14.19.11 (2)"]
#check (inferInstance :
  (SimplexCategory.Truncated.inclusion k).op.HasPointwiseRightKanExtension F)

#check (Truncated.cosk k : SimplicialObject.Truncated C k ⥤ SimplicialObject C)

#check (coskAdj k : truncation k ⊣ Truncated.cosk k)

end Positive

end CategoryTheory
