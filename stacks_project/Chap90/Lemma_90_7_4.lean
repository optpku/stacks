/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

import StacksCheckRecall
public import ReasLib.AlgebraicGeometry.FormalDeformation.FiltrationEquivalence

/-!
# Independence of the completion fibre from the ideal filtration

The comparison functor from formal objects indexed by a cofinal ideal
filtration to the completion fibre is an equivalence.
-/

@[expose] public section

open CategoryTheory

universe u v

variable {Λ k : Type u} [CommRing Λ] [IsNoetherianRing Λ] [Field k] [Algebra Λ k]
  [Module.Finite Λ k]
variable {F : Type v} [Category.{v} F]

/- Lemma 90.7.4 -/
@[stacks 06H6] #check (FormalObject.Along.toFiber_isEquivalence :
  ∀ (p : F ⥤ ArtinianLocalAlgCat Λ k) [Functor.IsFibered.InGroupoids p.op]
    (R : CompleteLocalAlgCat Λ k)
    (I : CompleteLocalAlgCat.AdicIdealFiltration R),
    -- Local instance justification (defeq pin): the checked equivalence uses the explicit source category of the comparison functor.
    letI := FormalObject.Along.category (p := p) (R := R) (I := I)
    (FormalObject.Along.toFiber p R I).IsEquivalence)
