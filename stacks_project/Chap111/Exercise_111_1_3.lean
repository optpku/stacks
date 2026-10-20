module

public import ReasLib.Algebra.Module.SpanRankOperations
public import ReasLib.RingTheory.Flat.Ideal.LocalRing
import StacksCheckRecall

@[expose] public section

open TensorProduct

universe u v w

/- Exercise 111.1.3 (1): for finite modules `M` and `N` over a Noetherian local
ring `A`, the minimal number of generators of `M ⊗[A] N` is the product of
those of `M` and `N`. By NAK, `spanFinrank` equals the dimension modulo the
maximal ideal, as expressed by `IsLocalRing.spanFinrank_eq_finrank_quotient`,
and the dimension after residue-field base change, as expressed by
`TensorProduct.spanFinrank_top_eq_of_residueField`. -/
@[stacks 02CI] #check (IsLocalRing.spanFinrank_tensorProduct :
  ∀ {A : Type u} [CommRing A] [IsLocalRing A] [IsNoetherianRing A]
    {M : Type v} {N : Type w}
    [AddCommGroup M] [AddCommGroup N] [Module A M] [Module A N]
    [Module.Finite A M] [Module.Finite A N],
    (⊤ : Submodule A (M ⊗[A] N)).spanFinrank =
      (⊤ : Submodule A M).spanFinrank * (⊤ : Submodule A N).spanFinrank)

/- Exercise 111.1.3 (2): if `I` is an ideal with more than one generator, then
the minimal number of generators of `I ^ 2` is strictly smaller than the square
of that of `I`. -/
@[stacks 02CI] #check (IsLocalRing.spanFinrank_sq_lt :
  ∀ {A : Type u} [CommRing A] [IsLocalRing A] [IsNoetherianRing A]
    {I : Ideal A} (hI : 1 < I.spanFinrank),
    (I ^ 2).spanFinrank < I.spanFinrank ^ 2)

/- Exercise 111.1.3 (3): if every ideal of `A` is a flat `A`-module, then `A` is
a PID (or a field). -/
@[stacks 02CI] #check (IsLocalRing.isDomain_and_isPrincipalIdealRing_of_forall_ideal_flat :
  ∀ {A : Type u} [CommRing A] [IsLocalRing A] [IsNoetherianRing A]
    (hflat : ∀ I : Ideal A, Module.Flat A I),
    IsDomain A ∧ IsPrincipalIdealRing A)
