module

public import ReasLib.Algebra.Category.ModuleCat.Presheaf.Flat.RingColimit
import StacksCheckRecall

@[expose] public section

/-!
# Lemma 10.39.6

@stack 05UU

Flatness over a filtered colimit of rings can be checked stagewise, and a compatible filtered
colimit of flat modules is flat over the colimit ring.
-/

/- Lemma 10.39.6 (1): stagewise flatness after restriction of scalars implies flatness over the
colimit ring. -/
@[stacks 05UU "(1), stagewise restriction criterion"]
#check @PresheafOfModules.RingColimit.flat_of_stagewise_restrictScalars

/- Lemma 10.39.6 (2): a compatible colimit of stagewise flat modules is flat over the colimit
ring. -/
@[stacks 05UU "(2), colimit of stagewise flat modules"]
#check @PresheafOfModules.RingColimit.flat_colimitFunctor_of_stagewise_flat
