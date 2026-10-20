module

public import stacks_project.Chap47.Lemma_47_5_8
import StacksCheckRecall

@[expose] public section

universe u v w

/- Proposition 47.5.9 (Structure of injective modules over Noetherian rings) (1):
Every injective module over a commutative Noetherian ring is an internal direct sum of
indecomposable injective submodules. -/
@[stacks 08YA] #check
  (Module.Injective.exists_indecomposable_decomposition :
    ∀ (R : Type u) (E : Type v) [CommRing R] [IsNoetherianRing R]
      [AddCommGroup E] [Module R E] [Module.Injective R E],
      ∃ (ι : Type w) (summand : ι → Submodule R E),
        iSupIndep summand ∧ iSup summand = ⊤ ∧
          ∀ i, Module.Injective R (summand i) ∧
            CategoryTheory.Indecomposable (ModuleCat.of R (summand i)))

/- Proposition 47.5.9 (Structure of injective modules over Noetherian rings) (2):
Every indecomposable injective module is an injective hull of the residue field at a prime. -/
@[stacks 08YA] #check
  (Module.exists_isInjectiveHull_residueField_of_indecomposable :
    ∀ (R : Type u) (E : Type v) [CommRing R] [IsNoetherianRing R]
      [AddCommGroup E] [Module R E] [Module.Injective R E]
      (hE : CategoryTheory.Indecomposable (ModuleCat.of R E)),
      ∃ (p : Ideal R) (_ : p.IsPrime) (i : p.ResidueField →ₗ[R] E),
        i.IsInjectiveHull)
