module

import ReasLib.CategoryTheory.Abelian.Extension.Yoneda.Ext
import StacksCheckRecall

@[expose] public section

/-!
# Lemma 13.27.5

Positive-degree Yoneda extensions are compared with canonical derived-category `Ext` classes in
the neutral `YonedaExtension` API.  The chapter entry exposes the comparison map, its recursive
computation, its surjectivity, and the detection of Yoneda equivalence.
-/

/- Lemma 13.27.5: the canonical class of a positive-degree Yoneda extension. -/
@[stacks 06XU] #check @CategoryTheory.YonedaExtension.toExt

/- Lemma 13.27.5: the successor computation obtained by removing the head short exact
sequence. -/
@[stacks 06XU] #check @CategoryTheory.YonedaExtension.toExt_succ

/- Lemma 13.27.5: every positive-degree `Ext` class has a Yoneda representative. -/
@[stacks 06XU] #check @CategoryTheory.YonedaExtension.toExt_surjective

/- Lemma 13.27.5: equality of canonical `Ext` classes is exactly Yoneda equivalence. -/
@[stacks 06XU] #check @CategoryTheory.YonedaExtension.equivalent_iff_toExt_eq
