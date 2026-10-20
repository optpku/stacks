module

public import ReasLib.Algebra.Module.Torsion.FiniteEmbedding
import StacksCheckRecall

/-!
# Lemma 15.22.7

@stack 0AUU
-/

universe u v

/- Lemma 15.22.7 (0AUU): a finite module over a domain is torsion-free exactly when it embeds
linearly into a finite free module, expressed in the canonical model `Fin n → R`. -/
@[stacks 0AUU]
#check fun {R : Type u} {M : Type v} [CommRing R] [IsDomain R]
    [AddCommGroup M] [Module R M] [Module.Finite R M] ↦
  (Module.IsTorsionFree.iff_exists_injective_fin_fun (R := R) (M := M) :
    Module.IsTorsionFree R M ↔
      ∃ n : ℕ, ∃ f : M →ₗ[R] (Fin n → R), Function.Injective f)
