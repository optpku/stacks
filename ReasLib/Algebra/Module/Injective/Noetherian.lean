module

public import ReasLib.Algebra.Module.Injective.Indecomposable
public import ReasLib.Algebra.Module.Injective.Prime
public import Mathlib.RingTheory.Noetherian.Defs

@[expose] public section

universe u v w

/-- Every injective module over a commutative Noetherian ring is an internal direct sum
of injective indecomposable submodules. -/
theorem Module.Injective.exists_indecomposable_decomposition
    (R : Type u) (E : Type v) [CommRing R] [IsNoetherianRing R]
    [AddCommGroup E] [Module R E] [Module.Injective R E] :
    ∃ (ι : Type w) (summand : ι → Submodule R E),
      iSupIndep summand ∧ iSup summand = ⊤ ∧
        ∀ i, Module.Injective R (summand i) ∧
          CategoryTheory.Indecomposable (ModuleCat.of R (summand i)) := sorry

/-- Every indecomposable injective module over a commutative Noetherian ring is an
injective hull of the residue field at some prime ideal. -/
theorem Module.exists_isInjectiveHull_residueField_of_indecomposable
    (R : Type u) (E : Type v) [CommRing R] [IsNoetherianRing R]
    [AddCommGroup E] [Module R E] [Module.Injective R E]
    (hE : CategoryTheory.Indecomposable (ModuleCat.of R E)) :
    ∃ (p : Ideal R) (_ : p.IsPrime) (i : p.ResidueField →ₗ[R] E),
      i.IsInjectiveHull := sorry
