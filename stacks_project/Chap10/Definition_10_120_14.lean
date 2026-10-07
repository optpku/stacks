module

public import ReasLib.RingTheory.DedekindDomain.IdealFactorization
import StacksCheckRecall

/-!
# Dedekind domains via prime-ideal factorization

@stack 034W
-/

@[expose] public section

universe u

variable (R : Type u) [CommRing R]

/- Definition 10.120.14 (Stacks `034W`): the source's unique prime-ideal factorization
formulation is the reusable `IsDedekindDomainByFactorization` owner.  Its two clauses are
`IsDomain R` and `Ideal.HasUniquePrimeFactorization R`. -/
@[stacks 034W]
#check (IsDedekindDomainByFactorization R : Prop)

@[stacks 034W "prime ideal factorization"]
#check @Ideal.IsPrimeFactorization
@[stacks 034W "unique prime factorization predicate"]
#check @Ideal.HasUniquePrimeFactorization
@[stacks 034W "Dedekind factorization owner"]
#check @IsDedekindDomain.hasUniquePrimeFactorization
@[stacks 034W "factorization characterization"]
#check @isDedekindDomain_iff_isDedekindDomainByFactorization
