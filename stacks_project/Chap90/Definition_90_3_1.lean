module

public import stacks_project.Chap90.Definition_90_7_3_ArtinianLocal
public import stacks_project.Chap90.Definition_90_3_1_Classical
import StacksCheckRecall

/-!
# The base category of Artinian local algebras
-/

@[expose] public section

/- Definition 90.3.1 (1): the category of Artinian local `Λ`-algebras equipped with a
`Λ`-algebra identification of the residue field with a finite `Λ`-field `k`. -/
@[stacks 06GC]
#check ArtinianLocalAlgCat

#check ArtinianLocalAlgCat.Hom
#check ArtinianLocalAlgCat.category

/- Definition 90.3.1 (2): the classical case, when `Λ` is a Noetherian complete local
ring and `k` is its residue field. -/
@[stacks 06GC]
#check ArtinianLocalAlgCat.IsClassical
