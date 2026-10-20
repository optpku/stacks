/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.AlgebraicGeometry.Scheme.Module.SchemeTheoreticSupport.Proper
import StacksCheckRecall

@[expose] public section

open CategoryTheory
open AlgebraicGeometry

universe u

/- Lemma 30.26.7: for a locally finite type morphism `f : X ⟶ S` and a finite-type
quasicoherent `𝒪_X`-module `ℱ`, properness over `S` of the ordinary support, properness over `S`
of the scheme-theoretic support, and descent from a proper closed subscheme are equivalent. -/
@[stacks 0CYS] #check
  (AlgebraicGeometry.Scheme.Modules.moduleSupport_properOver_tfae_schemeTheoreticSupport_and_pushforward :
    ∀ {X S : Scheme.{u}} (f : X ⟶ S) [LocallyOfFiniteType f]
      (ℱ : X.Modules) [ℱ.IsFiniteType] [ℱ.IsQuasicoherent],
      List.TFAE [
        ClosedSubset.IsProperOver f (Scheme.Modules.closedSupport ℱ),
        IsProper ((Scheme.Modules.schemeTheoreticSupport ℱ).subschemeι ≫ f),
        ∃ I : X.IdealSheafData,
          ∃ 𝒢 : I.subscheme.Modules,
            ∃ _ : 𝒢.IsFiniteType,
              ∃ _ : 𝒢.IsQuasicoherent,
                ∃ _ : IsProper (I.subschemeι ≫ f),
                  Nonempty ((Scheme.Modules.pushforward I.subschemeι).obj 𝒢 ≅ ℱ)
      ])
