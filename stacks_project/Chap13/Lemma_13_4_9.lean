module

import ReasLib.CategoryTheory.Pretriangulated.Triangle.Zero
import StacksCheckRecall

@[expose] public section

/-!
# Lemma 13.4.9

The fixed-morphism zero-cone criteria are reusable `Pretriangulated` API;
they deliberately quantify over distinguished completions rather than choose
a cone object.
-/

@[stacks 05QR] #check @CategoryTheory.Pretriangulated.isIso_iff_forall_isZero_obj₃_of_distinguished

@[stacks 05QR] #check @CategoryTheory.Pretriangulated.isIso_iff_zeroCone_distinguished
