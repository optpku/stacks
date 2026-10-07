module

import StacksCheckRecall
public import ReasLib.RingTheory.Smooth.Standard.Normalized

/-!
# Lemma 16.3.6 compatibility façade

The linear-presentation computation and normalized standard-smooth
presentation APIs are neutral infrastructure. They are owned by
`ReasLib.RingTheory.Smooth.Standard.{Linear,Normalized}`; this file preserves
the historical Chapter 16 import path.
-/

@[expose] public section

universe u v

namespace Algebra

open LinearPresentation

/- Lemma 16.3.6: a standard-smooth algebra admits a normalized finite
submersive presentation containing a prescribed finite family of generators. -/
#check @relation
#check @ideal
#check @quotientEquiv
#check @quotientEquiv_mk_eq_aeval
#check @submersive
#check @IsStandardSmooth.exists_presentation_containing
#check @SubmersivePresentation.exists_reindex_extending
#check @SubmersivePresentation.exists_finReindex_extending
@[stacks 07EY]
#check @IsStandardSmooth.exists_finPresentation_containing

end Algebra
