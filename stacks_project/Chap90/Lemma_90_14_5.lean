/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.AlgebraicGeometry.FormalDeformation.FormalObject.MinimalVersal
import StacksCheckRecall

/-!
# Minimal versal formal objects

A predeformation category with a versal formal object admits a minimal versal
formal object, unique up to isomorphism; every versal object is the pushforward
of a minimal versal object along a power series ring extension.
-/

@[expose] public section

open CategoryTheory
open CompleteLocalAlgCat

universe u

variable {Λ k : Type u} [CommRing Λ] [IsNoetherianRing Λ] [Field k] [Algebra Λ k]
  [Module.Finite Λ k]
variable {F : Type (u + 1)} [Category.{u + 1} F]
variable {p : F ⥤ ArtinianLocalAlgCat Λ k}

/- Lemma 90.14.5 (1): a predeformation category with a versal formal object has
a minimal versal formal object. -/
@[stacks 06T5] #check (FormalObject.exists_isMinimalVersal :
  ∀ [Functor.IsPredeformationCategory p] (ξ : FormalObject p) [FormalObject.IsVersal ξ],
    ∃ ξ' : FormalObject p, FormalObject.IsMinimalVersal ξ')

/- Lemma 90.14.5 (2): minimal versal formal objects are unique up to isomorphism. -/
@[stacks 06T5] #check (FormalObject.nonempty_iso :
  ∀ [Functor.IsPredeformationCategory p] (ξ η : FormalObject p)
    [FormalObject.IsMinimalVersal ξ] [FormalObject.IsMinimalVersal η],
    Nonempty (ξ ≅ η))

/- Lemma 90.14.5 (3): every versal formal object is the pushforward of a minimal
versal formal object along a finite-variable power series extension. -/
@[stacks 06T5] #check (FormalObject.exists_isPowerSeriesOver :
  ∀ [Functor.IsPredeformationCategory p] (ξ : FormalObject p) [FormalObject.IsVersal ξ],
    ∃ (ξ' : FormalObject p) (f : ξ' ⟶ ξ),
      FormalObject.IsMinimalVersal ξ' ∧ CompleteLocalAlgCat.IsPowerSeriesOver f.base)

#check (FormalObject.isIso :
  ∀ [Functor.IsPredeformationCategory p] {ξ η : FormalObject p}
    [FormalObject.IsMinimalVersal ξ] [FormalObject.IsMinimalVersal η]
    (f : ξ ⟶ η), IsIso f)
