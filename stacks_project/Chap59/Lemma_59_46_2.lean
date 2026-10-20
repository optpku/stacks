/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.AlgebraicGeometry.Scheme.Cover.ClosedImmersion
import StacksCheckRecall

open CategoryTheory
open CategoryTheory.Limits
open AlgebraicGeometry

universe u v

@[expose] public section

/- Lemma 59.46.2: for a closed immersion `i : Z ⟶ X` and an étale morphism
`V ⟶ Z`, the scheme `V` has a Zariski covering by the pullbacks of étale
schemes over `X`. -/
@[stacks 04FW] #check
  (AlgebraicGeometry.exists_zariskiCover_of_closedImmersion_etale :
    ∀ {X Z V : Scheme.{u}} (i : Z ⟶ X) [IsClosedImmersion i]
      (v : V ⟶ Z) [Etale v],
      ∃ (I : Type v) (U : I → Scheme.{u}) (u : ∀ j, U j ⟶ X),
        (∀ j, Etale (u j)) ∧
          ∃ (w : ∀ j, (pullback (u j) i : Scheme.{u}) ⟶ V),
            (∀ j, pullback.snd (u j) i = w j ≫ v) ∧
              Presieve.ofArrows (fun j ↦ (pullback (u j) i : Scheme.{u})) w ∈
                Scheme.zariskiPrecoverage V)
