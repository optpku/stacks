module

public import stacks_project.Chap90.Remark_90_7_6_TypesCompletion
import StacksCheckRecall

/-!
# Set-valued completion of a functor on `C_Λ`

Identifying functors with cofibered sets, the completion of a functor
`F : ArtinianLocalAlgCat Λ k ⥤ Type w` is `Functor.typesCompletion F`.
-/

@[expose] public section

open CategoryTheory

/- Remark 90.7.6: identifying functors with cofibered sets, the completion of
`F : ArtinianLocalAlgCat Λ k ⥤ Type w` is the functor
`Functor.typesCompletion F : CompleteLocalAlgCat Λ k ⥤ Type w` given by
`(typesCompletion F).obj S = limit (S.truncationSystem ⋙ F)`, matching
`hat{F}(S) = lim F(S ⧸ m_S^n)`. This agrees with the definition in
Schlessinger's paper. -/
@[stacks 06H8] #check Functor.typesCompletion
