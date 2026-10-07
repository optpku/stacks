module

import StacksCheckRecall
public import ReasLib.Algebra.Module.ContentIdeal.Map.Local

/-!
# Lemma 15.24.3

The local closed-fiber criterion is recalled together with its universally
injective core.

@stack 0ASC
-/

@[expose] public section

universe u v w

/- Lemma 15.24.3: a map of flat modules over a local ring preserves content
ideals when its reduction modulo the maximal ideal is injective. -/
@[stacks 0ASC "Lemma 15.24.3"]
#check fun (A : Type u) (M : Type v) (N : Type w)
    [CommRing A] [IsLocalRing A]
    [AddCommGroup M] [Module A M] [Module.Flat A M]
    [AddCommGroup N] [Module A N] [Module.Flat A N]
    {x : M} {I : Ideal A} (hI : IsContentIdeal x I)
    (f : M →ₗ[A] N)
    (hf : Function.Injective
      (f.quotientMapByIdeal (IsLocalRing.maximalIdeal A))) ↦
  hI.map_of_injective_mod_maximalIdeal f hf

/- Tensor-stable injectivity gives the general transport API. -/
#check @IsContentIdeal.map_of_universallyInjective
