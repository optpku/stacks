module

public import ReasLib.Algebra.Module.Injective.Essential
import StacksCheckRecall

@[expose] public section

universe u v

/- Lemma 47.3.5 (1): A submodule `E` of an injective `R`-module `I` is injective if
and only if every submodule `E'` of `I` containing `E` in which `E` is essential is
equal to `E`. -/
@[stacks 08XS]
#check (Submodule.injective_iff_eq_of_essential_extension :
  ∀ {R : Type u} [Ring R] {I : Type v} [AddCommGroup I] [Module R I]
    [Module.Injective R I] (E : Submodule R I),
    Module.Injective R E ↔
      ∀ E' : Submodule R I, E ≤ E' →
        (∀ P : Submodule R I, P ≤ E' → P ≠ ⊥ → E ⊓ P ≠ ⊥) → E = E')

/- Lemma 47.3.5 (2): An `R`-module is injective if and only if every injective
linear map from it whose range is essential is surjective. -/
@[stacks 08XS]
#check (Module.injective_iff_surjective_of_essential_extension :
  ∀ {R : Type u} [Ring R] (E : Type v) [AddCommGroup E] [Module R E],
    Module.Injective R E ↔
      ∀ {M : Type v} [AddCommGroup M] [Module R M] (f : E →ₗ[R] M),
        Function.Injective f →
          (∀ P : Submodule R M, P ≠ ⊥ → LinearMap.range f ⊓ P ≠ ⊥) →
            Function.Surjective f)
