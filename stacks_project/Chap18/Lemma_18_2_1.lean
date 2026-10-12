/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import Mathlib.Algebra.Category.Grp.Abelian
public import Mathlib.CategoryTheory.Limits.FunctorCategory.Basic
import StacksCheckRecall

@[expose] public section

open CategoryTheory CategoryTheory.Limits Opposite

universe u v u₁ v₁

variable {C : Type u} [Category.{v} C]
variable {K : Type u₁} [Category.{v₁} K]
variable (U : C)

/- Lemma 18.2.1 (03CL), limits: abelian presheaves have all pointwise K-shaped limits. -/
@[stacks 03CL "limits"]
#check (inferInstance :
  HasLimitsOfShape K (Cᵒᵖ ⥤ AddCommGrpCat.{max u v u₁ v₁}))

/- Lemma 18.2.1 (03CL), colimits: abelian presheaves have all pointwise K-shaped colimits. -/
@[stacks 03CL "colimits"]
#check (inferInstance :
  HasColimitsOfShape K (Cᵒᵖ ⥤ AddCommGrpCat.{max u v u₁ v₁}))

/- Lemma 18.2.1 (03CL), sections and limits: evaluation over U preserves limits. -/
@[stacks 03CL "sections preserve limits"]
#check (inferInstance :
  PreservesLimitsOfShape K
    ((evaluation Cᵒᵖ AddCommGrpCat.{max u v u₁ v₁}).obj (op U)))

/- Lemma 18.2.1 (03CL), sections and colimits: evaluation over U preserves colimits. -/
@[stacks 03CL "sections preserve colimits"]
#check (inferInstance :
  PreservesColimitsOfShape K
    ((evaluation Cᵒᵖ AddCommGrpCat.{max u v u₁ v₁}).obj (op U)))
