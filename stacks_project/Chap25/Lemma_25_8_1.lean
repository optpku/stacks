module

public import ReasLib.CategoryTheory.Sites.Hypercovering.InternalHom
import StacksCheckRecall

/-!
# Restriction across one simplex

The shared owner uses the standard `SSet.Subcomplex.singleSimplex.Degreewise` attachment data
and mathlib's `SSet.Finite` and `SSet.Nonempty` classes.
-/

open CategoryTheory

/- Lemma 25.8.1 (01GM): restriction in degree zero along a finite nonempty single-simplex
extension is a covering morphism for every hypercovering. -/
@[stacks 01GM] #check @Hypercovering.InternalHom.PrecompZero.ofSingleSimplex

/- The underlying reusable theorem only needs the corresponding boundary pushout. -/
#check @Hypercovering.InternalHom.PrecompZero.ofBoundaryPushout
