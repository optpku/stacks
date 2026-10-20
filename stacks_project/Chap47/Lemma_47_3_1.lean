module

public import ReasLib.Algebra.Module.Injective.Product
import StacksCheckRecall

universe u v w

/- Lemma 47.3.1: for a ring `R` and a family `M` of injective `R`-modules, the
product module `(i : ι) → M i` is injective. -/
@[stacks 08XP] #check
  (Module.Injective.product :
    ∀ (R : Type u) [Ring R] {ι : Type w} (M : ι → Type v) [Small.{v} R]
      [∀ i, AddCommGroup (M i)] [∀ i, Module R (M i)] [∀ i, Module.Injective R (M i)],
      Module.Injective R ((i : ι) → M i))
