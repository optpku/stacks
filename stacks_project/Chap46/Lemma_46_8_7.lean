/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.Algebra.Category.ModuleCat.PureInjective.Resolution.Comparison
import StacksCheckRecall

@[expose] public section

open CategoryTheory

universe u v

variable {A : Type u} [CommRing A]

/- Lemma 46.8.7 (1): every module has a pure injective resolution. -/
@[stacks 0704] #check
  (ModuleCat.existsPureInjectiveResolution :
    ∀ (M : ModuleCat.{v} A), Nonempty (ModuleCat.PureInjectiveCoresolution M))

/- Lemma 46.8.7 (2): a map `M ⟶ N` extends from a universally exact coresolution of
`M` to a pure injective resolution of `N`. -/
@[stacks 0704] #check
  (ModuleCat.PureInjectiveCoresolution.existsLift :
    ∀ {M N : ModuleCat.{v} A} (P : ModuleCat.UniversallyExactCoresolution M)
      (I : ModuleCat.PureInjectiveCoresolution N) (f : M ⟶ N),
      ∃ φ : P.cocomplex ⟶ I.cocomplex, P.ι ≫ φ.f 0 = f ≫ I.ι)

/- Lemma 46.8.7 (3): two maps from a universally exact coresolution to a pure injective
resolution that induce the same map on the resolved modules are homotopic. -/
@[stacks 0704] #check
  (ModuleCat.PureInjectiveCoresolution.homotopyOfLifts :
    ∀ {M N : ModuleCat.{v} A} (P : ModuleCat.UniversallyExactCoresolution M)
      (I : ModuleCat.PureInjectiveCoresolution N) (f : M ⟶ N)
      (α β : P.cocomplex ⟶ I.cocomplex),
      P.ι ≫ α.f 0 = f ≫ I.ι → P.ι ≫ β.f 0 = f ≫ I.ι →
        homotopic (ModuleCat A) (ComplexShape.up ℕ) α β)
