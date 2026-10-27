/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.Algebra.Category.CommRingCat.Under.ModuleValuedFunctor.Tangent.Injective
import StacksCheckRecall

@[expose] public section

open CategoryTheory CategoryTheory.Limits

universe u

namespace ModuleValuedFunctor

/-
Source mapping defect: Lemma 46.4.4 (Stacks tag 06ZA) originally claims that,
for every injective module-valued functor I, every algebra B and every short
exact sequence 0 → N₁ → N → N₂ → 0 of B-modules, the sequence
TI(B, N₁) → TI(B, N) → TI(B, N₂) → 0 is exact.

That assertion is false. Over k = F₂, coinduction from the injective
E-module Hom_k(E,k), where E = k[e]/(e²), gives an injective I whose tangent
fails exactness on the split sequence k → k² → k: the middle kernel has
16 elements while the preceding image has 4. The source proof's free-module
equalizer step ignores coefficient cancellation.

The following check refers to the honest counterstatement, whose proof is
still a Prop proof debt. It is a source correction, not a weakened version
or a formal proof of the original lemma. No Stacks certification attribute
is attached. The conclusions of 06ZG, 06ZH and 06ZI are not refuted here;
their source argument using 06ZA requires an independent repair.
-/
#check (ModuleValuedFunctor.exists_injective_tangent_not_exact.{u} :
  ∃ (A : CommRingCat.{u}) (I : ModuleValuedFunctor.{u, u} A),
    ModuleValuedFunctor.IsInjective I ∧
      ∃ (B : Under A) (S : ShortComplex (ModuleCat.{u} B.right)),
        S.ShortExact ∧
          ¬ (ComposableArrows.mk₂ ((I.tangent.fixedBase B).map S.f)
            ((I.tangent.fixedBase B).map S.g)).Exact)

end ModuleValuedFunctor
