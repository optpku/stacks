module

public import ReasLib.CategoryTheory.Sites.Localization.CategoryOfElements.Embedding
public import StacksCheckRecall.CommandCrossRef

/-!
# Lemma 7.43.3

The subterminal/localization-embedding comparison is a reusable localization
bridge and is owned by ReasLib.
-/

@[expose] public section

/- Lemma 7.43.3 (08LW): a sheaf is a subobject of the terminal sheaf exactly
when its category-of-elements localization is an embedding of topoi. -/
@[stacks 08LW] #check @CategoryTheory.Sheaf.Localization.mono_terminal_from_iff_isEmbedding
