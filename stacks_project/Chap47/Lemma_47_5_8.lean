module

public import ReasLib.Algebra.Module.Injective.Noetherian
import StacksCheckRecall

@[expose] public section

universe u v

/- Lemma 47.5.8: Every indecomposable injective module over a commutative Noetherian
ring is an injective hull of the residue field at some prime ideal. -/
@[stacks 08Y9] #check (Module.exists_isInjectiveHull_residueField_of_indecomposable :
  ∀ (R : Type u) (E : Type v) [CommRing R] [IsNoetherianRing R]
    [AddCommGroup E] [Module R E] [Module.Injective R E]
    (hE : CategoryTheory.Indecomposable (ModuleCat.of R E)),
    ∃ (p : Ideal R) (_ : p.IsPrime) (i : p.ResidueField →ₗ[R] E),
      i.IsInjectiveHull)
