module

public import ReasLib.Algebra.Module.ContentIdeal.ValuationRing
import StacksCheckRecall

@[expose] public section

universe u v w

/- Lemma 38.19.6: every element of a finite module over a local essentially
finite-type algebra, flat over a valuation ring, has a principal content ideal. -/
@[stacks 0ASX] #check
  (Module.Flat.existsPrincipalContentIdeal_of_valuationRing :
    ∀ {A : Type u} {B : Type v} {N : Type w}
      [CommRing A] [IsDomain A] [ValuationRing A]
      [CommRing B] [Algebra A B] [IsLocalRing B]
      [IsLocalHom (algebraMap A B)] [Algebra.EssFiniteType A B]
      [AddCommGroup N] [Module B N] [Module A N] [IsScalarTower A B N]
      [Module.Finite B N] [Module.Flat A N] (n : N),
      ∃ I : Ideal A, IsContentIdeal n I ∧ I.IsPrincipal)
