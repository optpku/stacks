module

public import stacks_project.Chap90.Definition_90_27_1_MinimalVersal
import StacksCheckRecall

@[expose] public section

/- Definition 90.8.9: let F be a category cofibered in groupoids. Let ξ be a
formal object of F lying over R in Ob(Ĉ_Λ). We say ξ is versal if the
corresponding morphism underline ξ : underline R |_{C_Λ} ⟶ F of Remark 90.7.12
is smooth. This is owned by FormalObject.IsVersal. -/
@[stacks 06HR] #check FormalObject.IsVersal

#check FormalObject.IsVersal.spec
