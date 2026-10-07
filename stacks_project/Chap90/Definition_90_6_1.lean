module

public import stacks_project.Chap90.Definition_90_6_1_Prorepresentable
import StacksCheckRecall

@[expose] public section

open CategoryTheory

/- Definition 90.6.1: a functor `F : ArtinianLocalAlgCat Λ k ⥤ Type u` is prorepresentable
if there exists `R : CompleteLocalAlgCat Λ k` with `F ≅ restrictedCoyoneda R`. -/
@[stacks 06GX]
#check Functor.IsProrepresentable
