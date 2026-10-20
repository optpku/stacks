module

public import ReasLib.Algebra.Category.ModuleCat.AdicComplete
import StacksCheckRecall

/-!
# The category of complete modules is not abelian
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits

universe u v

/- Lemma 110.10.1 (1): the category of `I`-adically complete `R`-modules has
kernels when `I` is finitely generated. -/
@[stacks 07JR] #check (ModuleCat.AdicComplete.hasKernels :
  ∀ {R : Type u} [CommRing R] (I : Ideal R),
    I.FG → HasKernels (ModuleCat.AdicComplete.category I))

/- Lemma 110.10.1 (2): the category of `I`-adically complete `R`-modules has
cokernels when `I` is finitely generated. -/
@[stacks 07JR] #check (ModuleCat.AdicComplete.hasCokernels :
  ∀ {R : Type u} [CommRing R] (I : Ideal R),
    I.FG → HasCokernels (ModuleCat.AdicComplete.category I))

/- Lemma 110.10.1 (3): the category of `I`-adically complete modules is not
abelian in general, even when `R` is Noetherian. -/
@[stacks 07JR] #check (ModuleCat.AdicComplete.exists_noetherian_not_abelian :
    ∃ (R : Type u) (_ : CommRing R) (_ : IsNoetherianRing R) (I : Ideal R),
      I.FG ∧ ¬ Nonempty (Abelian (ModuleCat.AdicComplete.category I)))
