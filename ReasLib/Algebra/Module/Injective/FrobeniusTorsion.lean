module

public import Mathlib.Algebra.Category.ModuleCat.ChangeOfRings
public import Mathlib.Algebra.DirectSum.Module
public import Mathlib.RingTheory.RegularLocalRing.Defs
public import ReasLib.Algebra.CharP.Frobenius
public import ReasLib.Algebra.Module.IdealPower.Predicate
public import ReasLib.Algebra.Module.Injective.Hull

@[expose] public section

open CategoryTheory

universe u v w

namespace Module

/-- Over a regular local ring `A` of prime characteristic `p`, a module that is
power torsion for the maximal ideal and is invariant under scalar extension along
Frobenius is isomorphic to a direct sum of copies of an injective hull of the
residue field. -/
theorem equivDirectSumInjectiveHull_of_frobeniusBaseChange
    (p : ℕ) [Fact p.Prime] {A : Type u} [CommRing A] [IsRegularLocalRing A]
    (hp : (p : A) = 0) (M : Type (max u v)) (E : Type w)
    [AddCommGroup M] [Module A M] [AddCommGroup E] [Module A E]
    [Module.Injective A E] (ι : IsLocalRing.ResidueField A →ₗ[A] E)
    (hι : ι.IsInjectiveHull)
    (hM : Module.IsIdealPowerTorsion (IsLocalRing.maximalIdeal A) M)
    (hF : Nonempty
      ((ModuleCat.extendScalars (RingHom.frobeniusOfPrime p hp)).obj
        (ModuleCat.of A M) ≅ ModuleCat.of A M)) :
    ∃ J : Type (max u v), Nonempty (M ≃ₗ[A] DirectSum J (fun _ ↦ E)) := sorry

end Module
