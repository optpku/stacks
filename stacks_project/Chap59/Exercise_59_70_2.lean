/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import stacks_project.Chap59.Definition_59_70_1
import StacksCheckRecall

@[expose] public section

open CategoryTheory
open AlgebraicGeometry

noncomputable section

universe u w

variable {U X : Scheme.{u}}

namespace AlgebraicGeometry.Scheme

variable (j : U ⟶ X) [Etale j]
    [∀ F : U.Etaleᵒᵖ ⥤ AddCommGrpCat.{w},
      (etaleRestriction j).op.HasLeftKanExtension F]
    [HasWeakSheafify X.smallEtaleTopology AddCommGrpCat.{w}]

/- Exercise 59.70.2: the sheafified abelian-group-valued extension-by-zero
functor `abelianExtensionByZero j` is left adjoint to the étale restriction
functor `etaleRestrictionSheaf j AddCommGrpCat.{w}`. -/
@[stacks 03S4] #check
  (AlgebraicGeometry.Scheme.abelianExtensionByZero_adjunction j :
    abelianExtensionByZero j ⊣ etaleRestrictionSheaf j AddCommGrpCat.{w})

end AlgebraicGeometry.Scheme
