module

public import StacksCheckRecall.CommandCrossRef
public import ReasLib.CategoryTheory.Sites.Sheaf.Hom
import StacksCheckRecall

/-!
# Lemma 7.26.2

The generic localized sheaf-Hom comparison and cartesian-closed currying API
are owned by ReasLib. This file retains the source label as a thin recall.
-/

@[expose] public section

/- 0BWQ (Lemma 7.26.2): for Type-valued sheaves on a site, morphisms
`F ⨯ G ⟶ H` are canonically in bijection with morphisms `F ⟶ sheafHom G H`. -/
@[stacks 0BWQ] #check @CategoryTheory.Sheaf.Hom.curryEquiv

/- Companion APIs expose the underlying internal-Hom comparison and evaluation map. -/
#check @CategoryTheory.Presheaf.Hom.functorHomIso
#check @CategoryTheory.Sheaf.Hom.Functor.ihomIso
#check @CategoryTheory.Sheaf.Hom.eval
