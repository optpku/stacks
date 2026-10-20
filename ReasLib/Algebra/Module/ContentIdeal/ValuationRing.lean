module

public import ReasLib.Algebra.Module.ContentIdeal.Finite
public import ReasLib.Algebra.Module.ContentIdeal.MittagLeffler
public import ReasLib.RingTheory.Flatness.MittagLeffler.Henselian
public import ReasLib.RingTheory.Valuation.Characterization
import Mathlib.Tactic.CrossRefAttribute

@[expose] public section

universe u v w

namespace Module.Flat

/-- Every element of a finite module over a local essentially finite-type algebra, flat over a
valuation ring, has a principal content ideal. -/
@[stacks 0ASX]
theorem existsPrincipalContentIdeal_of_valuationRing
    {A : Type u} {B : Type v} {N : Type w}
    [CommRing A] [IsDomain A] [ValuationRing A]
    [CommRing B] [Algebra A B] [IsLocalRing B]
    [IsLocalHom (algebraMap A B)] [Algebra.EssFiniteType A B]
    [AddCommGroup N] [Module B N] [Module A N] [IsScalarTower A B N]
    [Module.Finite B N] [Module.Flat A N] (n : N) :
    ∃ I : Ideal A, IsContentIdeal n I ∧ I.IsPrincipal := sorry

end Module.Flat
