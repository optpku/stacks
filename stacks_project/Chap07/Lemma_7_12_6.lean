module

public import ReasLib.CategoryTheory.Sites.SheafifiedRepresentable.Colimit
public import StacksCheckRecall.CommandCrossRef

/-!
# Lemma 7.12.6 recall

The generic colimit-density theorem for sheafified representables belongs to
ReasLib. This source file retains only the labeled textbook recall.
-/

@[expose] public section

/- Lemma 7.12.6 (0GLW): every set-valued sheaf is a small colimit of
sheafified representables. -/
@[stacks 0GLW] #check @CategoryTheory.GrothendieckTopology.SheafifiedRepresentable.existsColimitPresentation
