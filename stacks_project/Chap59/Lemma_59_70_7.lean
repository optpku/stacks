module

public import stacks_project.Chap59.Lemma_59_70_6
import StacksCheckRecall

@[expose] public section

open CategoryTheory
open AlgebraicGeometry

noncomputable section

universe u w

namespace AlgebraicGeometry.Scheme

variable {U X : Scheme.{u}} (j : U ⟶ X) [IsFinite j] [Etale j]

variable
    [∀ G : U.Etaleᵒᵖ ⥤ AddCommGrpCat.{w},
      (etaleRestriction j).op.HasLeftKanExtension G]
    [HasWeakSheafify X.smallEtaleTopology AddCommGrpCat.{w}]

/- Lemma 59.70.7 (1): for a finite étale morphism `j`, the comparison
`abelianExtensionByZeroToDirectImage j` is an isomorphism on every abelian sheaf. -/
@[stacks 03S7] #check
  (AlgebraicGeometry.Scheme.abelianExtensionByZeroToDirectImage_app_isIso j :
    ∀ F : Sheaf U.smallEtaleTopology AddCommGrpCat.{w},
      IsIso ((abelianExtensionByZeroToDirectImage j).app F))

variable {Λ : Type w} [Ring Λ]

variable
    [∀ G : U.Etaleᵒᵖ ⥤ ModuleCat.{w} Λ,
      (etaleRestriction j).op.HasLeftKanExtension G]
    [HasWeakSheafify X.smallEtaleTopology (ModuleCat.{w} Λ)]

/- Lemma 59.70.7 (2): for a finite étale morphism `j`, the comparison
`moduleExtensionByZeroToDirectImage j` is an isomorphism on every sheaf of
`Λ`-modules. -/
@[stacks 03S7] #check
  (AlgebraicGeometry.Scheme.moduleExtensionByZeroToDirectImage_app_isIso j :
    ∀ F : Sheaf U.smallEtaleTopology (ModuleCat.{w} Λ),
      IsIso ((moduleExtensionByZeroToDirectImage j).app F))

end AlgebraicGeometry.Scheme
