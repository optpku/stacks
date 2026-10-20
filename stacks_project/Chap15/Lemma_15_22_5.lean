/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.Algebra.Module.Torsion.Exact
import StacksCheckRecall

/-!
# Lemma 15.22.5

@stack 0AUS
-/

universe u v w x

/- Lemma 15.22.5 (0AUS): in a short exact sequence of modules over a domain, torsion-freeness of
the two end terms implies torsion-freeness of the middle term. -/
@[stacks 0AUS]
#check fun {R : Type u} [CommRing R] [IsDomain R]
    {M : Type v} {M' : Type w} {M'' : Type x}
    [AddCommGroup M] [Module R M] [AddCommGroup M'] [Module R M']
    [AddCommGroup M''] [Module R M''] {f : M →ₗ[R] M'} {g : M' →ₗ[R] M''}
    (hfg : Function.Exact f g) (hf : Function.Injective f) (_ : Function.Surjective g)
    [Module.IsTorsionFree R M] [Module.IsTorsionFree R M''] ↦
  (Module.IsTorsionFree.of_exact_of_injective hfg hf : Module.IsTorsionFree R M')
