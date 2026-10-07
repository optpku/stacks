module

import StacksCheckRecall
public import ReasLib.Algebra.Module.IdealPower.Quotient.Iso.Noetherian

/-!
# Lemma 15.101.5

@stack 09BC
-/

@[expose] public section

open CategoryTheory
open CategoryTheory.Limits
open Ideal.PowerQuotient

/- Lemma 15.101.5 (09BC): let `R` be Noetherian, let `I : Ideal R`, and let
`M` and `N` be finite `R`-modules.  If the quotients of `M` and `N` by every
positive power of `I` are linearly isomorphic, then their `I`-adic completions
are linearly isomorphic over `AdicCompletion I R`.

Stage `n : ℕ` below represents quotienting by `I ^ (n + 1)`.  The hypothesis
asserts only stagewise existence; the Mittag-Leffler API supplies a compatible
family. -/
@[stacks 09BC "isomorphic completions from isomorphic ideal-power quotients"]
#check @Iso.nonempty_completionEquiv_of_stagewise

/- The two reusable steps are exposed at the chapter boundary: first construct
a compatible limit point, then turn it into an equivalence of completions. -/
#check @Iso.nonempty_limit_of_stagewise
#check @Iso.system_isMittagLeffler
#check @Iso.limitComparison
#check @Iso.limitComparison_bijective
#check @Iso.stage
#check @Iso.system
