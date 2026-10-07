module

public import ReasLib.RingTheory.QuasiFinite.MinimalPrime
import StacksCheckRecall

/-!
# Finiteness after removing a minimal-prime fiber

@stack 02ML

The reusable finite-away-neighborhood statement is owned by ReasLib. This
entry records the source label and recalls that canonical declaration.
-/

@[expose] public section

/- Lemma 10.122.11 (02ML): if `R → S` is of finite type, `p` is a minimal
prime of `R`, and only finitely many primes of `S` lie over `p`, then there is
`g ∈ R \ p` for which the localized map `R_g → S_g` is finite. -/
@[stacks 02ML "finite away neighborhood of a minimal prime"]
#check @Algebra.FiniteType.exists_away_finite_of_finite_primesOver_minimalPrime

#check @Ideal.primesOver
#check @Localization.awayMapₐ

end
