/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.Algebra.Category.ModuleCat.Descent.Pushforward
import StacksCheckRecall

@[expose] public section

open CategoryTheory
open CategoryTheory.Limits

universe u v w

variable {R : Type u} {S : Type v} [CommRing R] [CommRing S]
variable (f : R →+* S)
variable (D : (ModuleCat.extendRestrictScalarsAdj.{w} f).toComonad.Coalgebra)

/- 35.4.20.1: scalar extension of the canonical equalizer fork defining the
pushforward of `(M, θ)` gives the displayed fork. Under the canonical tensor
identifications, its inclusion is `θ ∘ (1_M ⊗ δ₀¹)`, and its parallel arrows
are `(θ ⊗ δ₂²) ∘ (1_M ⊗ δ₀²)` and `1_(M ⊗ S₂) ⊗ δ₁²`. -/
@[stacks 08X8] #check
  (ModuleCat.DescentPushforward.baseChangeFork f D :
    Fork ((ModuleCat.extendScalars f).map ((ModuleCat.restrictScalars f).map D.a))
      ((ModuleCat.extendScalars f).map
        ((ModuleCat.extendRestrictScalarsAdj f).unit.app
          ((ModuleCat.restrictScalars f).obj D.A))))
