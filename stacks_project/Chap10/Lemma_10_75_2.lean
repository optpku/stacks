/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import ReasLib.Algebra.Category.ModuleCat.Tor.Exact
import StacksCheckRecall

@[expose] public section

/-!
# Low-Degree `Tor` Sequence

@stack 00M0

The reusable `Tor` exact-sequence API is owned by
`ReasLib.Algebra.Category.ModuleCat.Tor.Exact`. This chapter
entry retains the source label and recalls the low-degree specialization.
-/

/- Lemma 10.75.2 (Stacks 00M0): for a short exact sequence
`0 → N' → N → N'' → 0` of `R`-modules, there is an exact row
`Tor₁^R(M, N') → Tor₁^R(M, N) → Tor₁^R(M, N'') → M ⊗[R] N' →
M ⊗[R] N → M ⊗[R] N'' → 0`.  In ReasLib the connecting morphism is
explicit data, supplied by the existential theorem below. -/
@[stacks 00M0]
#check @CategoryTheory.ModuleCat.Tor.exists_oneTensorSequence_exact

/- The reusable fine-grained windows and higher-degree long-exact segment. -/
@[stacks 00M0 "same-degree exactness"]
#check @CategoryTheory.ModuleCat.Tor.exact_of_shortExact
@[stacks 00M0 "low-degree boundary"]
#check @CategoryTheory.ModuleCat.Tor.exists_oneTensorBoundary_exact
@[stacks 00M0 "higher-degree five-term segment"]
#check @CategoryTheory.ModuleCat.Tor.exists_succFiveTerm_exact
