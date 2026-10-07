module

public import ReasLib.RingTheory.UniqueFactorizationDomain.Factorization
import StacksCheckRecall

/-!
# Unique Factorization from Irreducible Factorizations

@stack 034T
-/

@[expose] public section

universe u

variable {R : Type u} [CommRing R] [IsDomain R]

/- Lemma 10.120.5 (Stacks `034T`): in a domain where every nonzero nonunit has an
irreducible factorization, unique factorization is equivalent to every irreducible being prime. -/
@[stacks 034T]
#check (UniqueFactorizationMonoid.iff_forall_irreducible_prime (R := R) :
  UniqueFactorizationMonoid.HasIrreducibleFactorizations R →
    (UniqueFactorizationMonoid R ↔ ∀ a : R, Irreducible a → Prime a))

@[stacks 034T "irreducible-factorization predicate"]
#check @UniqueFactorizationMonoid.HasIrreducibleFactorizations

@[stacks 034T "map-level irreducible-prime criterion"]
#check @UniqueFactorizationMonoid.iff_forall_irreducible_prime
