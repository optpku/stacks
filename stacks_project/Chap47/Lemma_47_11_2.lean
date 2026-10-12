/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import ReasLib.RingTheory.Depth.IdealExact
import StacksCheckRecall

@[expose] public section

open CategoryTheory
open scoped ENat

universe u v

namespace CategoryTheory.ShortComplex.ShortExact

/- Lemma 47.11.2 (1) -/
@[stacks 0BUV] #check
  (CategoryTheory.ShortComplex.ShortExact.idealDepth_middle_ge_min :
    ∀ {A : Type u} [CommRing A] [IsNoetherianRing A]
      {S : ShortComplex (ModuleCat.{v} A)}
      [Module.Finite A S.X₁] [Module.Finite A S.X₂] [Module.Finite A S.X₃]
      (I : Ideal A) (hS : S.ShortExact),
      I.depth S.X₂ ≥ min (I.depth S.X₁) (I.depth S.X₃))

/- Lemma 47.11.2 (2) -/
@[stacks 0BUV] #check
  (CategoryTheory.ShortComplex.ShortExact.idealDepth_right_ge_min :
    ∀ {A : Type u} [CommRing A] [IsNoetherianRing A]
      {S : ShortComplex (ModuleCat.{v} A)}
      [Module.Finite A S.X₁] [Module.Finite A S.X₂] [Module.Finite A S.X₃]
      (I : Ideal A) (hS : S.ShortExact),
      I.depth S.X₃ ≥ min (I.depth S.X₂) (I.depth S.X₁ - 1))

/- Lemma 47.11.2 (3) -/
@[stacks 0BUV] #check
  (CategoryTheory.ShortComplex.ShortExact.idealDepth_left_ge_min :
    ∀ {A : Type u} [CommRing A] [IsNoetherianRing A]
      {S : ShortComplex (ModuleCat.{v} A)}
      [Module.Finite A S.X₁] [Module.Finite A S.X₂] [Module.Finite A S.X₃]
      (I : Ideal A) (hS : S.ShortExact),
      I.depth S.X₁ ≥ min (I.depth S.X₂) (I.depth S.X₃ + 1))

end CategoryTheory.ShortComplex.ShortExact
