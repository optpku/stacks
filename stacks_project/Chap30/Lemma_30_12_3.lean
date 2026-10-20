/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.AlgebraicGeometry.Scheme.Module.Coherent.Devissage
import StacksCheckRecall

@[expose] public section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits

noncomputable section

universe u

/- Lemma 30.12.3: on a Noetherian scheme, every coherent `𝒪_X`-module has a finite
filtration by coherent submodules whose successive quotients are pushforwards of nonzero coherent
ideal sheaves on integral closed subschemes. -/
@[stacks 01YF] #check (
  AlgebraicGeometry.Scheme.Modules.exists_coherentSubobject_filtration_quotient_iso_pushforward_ideal :
    ∀ {X : Scheme.{u}} [IsNoetherian X] (ℱ : X.Modules) [ℱ.IsCoherent],
      ∃ (m : ℕ) (F : ℕ →o Subobject ℱ)
        (Z : Fin m → X.IdealSheafData)
        (I : (j : Fin m) →
          Subobject (SheafOfModules.unit (Z j).subscheme.ringCatSheaf : (Z j).subscheme.Modules))
        (e : (j : Fin m) →
          cokernel (Subobject.ofLE (F j.1) (F (j.1 + 1)) (F.monotone (Nat.le_succ j.1))) ≅
            (Scheme.Modules.pushforward (Z j).subschemeι).obj
              (Subobject.underlying.obj (I j) : (Z j).subscheme.Modules)),
        ∃ (hBot : F 0 = ⊥) (hTop : F m = ⊤)
          (hFiltrationCoherent :
            ∀ n : ℕ, n ≤ m → ((F n : Subobject ℱ) : X.Modules).IsCoherent)
          (hIntegral : ∀ j : Fin m, IsIntegral (Z j).subscheme)
          (hIdealCoherent : ∀ j : Fin m,
            ((Subobject.underlying.obj (I j) : (Z j).subscheme.Modules)).IsCoherent),
          ∀ j : Fin m,
            I j ≠ (⊥ : Subobject
              (SheafOfModules.unit (Z j).subscheme.ringCatSheaf : (Z j).subscheme.Modules)))
