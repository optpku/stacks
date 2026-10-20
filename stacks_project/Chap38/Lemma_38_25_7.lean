/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.Algebra.Module.PureSpreadout
import StacksCheckRecall

@[expose] public section

universe u v w x y z

variable {A : Type u} {B : Type v} [CommRing A] [CommRing B] [Algebra A B]
variable (S : Submonoid B) {N : Type w} [AddCommGroup N]
variable [Module (Localization S) N] [Module B N] [Module A N]
variable [IsScalarTower B (Localization S) N] [IsScalarTower A B N]
variable [Module.FinitePresentation (Localization S) N]
variable {N' : Type x} [AddCommGroup N'] [Module B N'] [Module A N']
variable [IsScalarTower A B N'] [Module.FinitePresentation B N']
variable [Module.Projective A N']

/- Lemma 38.25.7 (1): a module admitting a pure spreadout has content ideals. -/
@[stacks 0AT7] #check (Module.PureSpreadout.existsContentIdeal (S := S) :
  (algebraMap A B).FinitePresentation →
    ∀ (ι : N' →ₗ[B] N) [IsLocalizedModule S ι],
      LinearMap.UniversallyInjective.{u, x, w, max u v w x}
          (ι.restrictScalars A) →
        ∀ n : N, ∃ I : Ideal A, IsContentIdeal n I)

/- Lemma 38.25.7 (2): a map from such a module to a flat module is universally
injective if it is injective modulo every maximal ideal. -/
@[stacks 0AT7] #check
  (Module.PureSpreadout.universallyInjective_of_injective_mod_maximalIdeal (S := S) :
    (algebraMap A B).FinitePresentation →
      ∀ (ι : N' →ₗ[B] N) [IsLocalizedModule S ι],
        LinearMap.UniversallyInjective.{u, x, w, max u v w x y z}
            (ι.restrictScalars A) →
          ∀ {M : Type y} [AddCommGroup M] [Module A M] [Module.Flat A M]
            (f : N →ₗ[A] M),
            (∀ (m : Ideal A) [m.IsMaximal],
              Function.Injective (f.quotientMapByIdeal m)) →
              LinearMap.UniversallyInjective.{u, w, y, max u v w x y z} f)
