/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import ReasLib.Algebra.Category.CommRingCat.Under.ModuleValuedFunctor.Tangent.Injective
import StacksCheckRecall

@[expose] public section

open CategoryTheory CategoryTheory.Limits

universe u

namespace ModuleValuedFunctor

/- Lemma 46.4.4: for an injective module-valued functor `I`, applying `TI(B, ·)` to a
short exact sequence of `B`-modules gives an exact composable pair whose second map is epic. -/
@[stacks 06ZA] #check (ModuleValuedFunctor.tangent_exact_and_epi_of_injective :
  ∀ {A : CommRingCat.{u}} (I : ModuleValuedFunctor.{u, u} A),
    ModuleValuedFunctor.IsInjective I →
    ∀ (B : Under A) (S : ShortComplex (ModuleCat.{u} B.right)), S.ShortExact →
      (ComposableArrows.mk₂ ((I.tangent.fixedBase B).map S.f)
        ((I.tangent.fixedBase B).map S.g)).Exact ∧
        Epi ((I.tangent.fixedBase B).map S.g))

end ModuleValuedFunctor
