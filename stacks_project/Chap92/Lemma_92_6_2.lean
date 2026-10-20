/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.RingTheory.CotangentComplex.DerivedBaseChange
import StacksCheckRecall

/-!
# Derived functoriality of the cotangent complex after a derived-tensor quasi-isomorphism

If a commutative square of rings induces a quasi-isomorphism `B ⊗[A]^L A' = B'`, the
Section 92.6 functoriality map becomes an isomorphism
`L_{B/A} ⊗[B]^L B' ⟶ L_{B'/A'}` in `D(B')`.
-/

@[expose] public section

open CategoryTheory
open RingedSite.Cotangent.Functoriality

universe u

variable {A B A' B' : CommRingCat.{u}}
variable {α : A ⟶ B} {ρ : A ⟶ A'} {β : A' ⟶ B'} {φ : B ⟶ B'}

/- Lemma 92.6.2. If the commutative square (92.6.0.1) induces a quasi-isomorphism
`B ⊗[A]^L A' = B'`, then the functoriality map induces an isomorphism
`L_{B/A} ⊗[B]^L B' ⟶ L_{B'/A'}` in `D(B')`. -/
@[stacks 08QQ] #check (Algebra.CotangentComplex.mapDerived_isIso :
  ∀ (sq : CommSq ρ α β φ), InducesDerivedTensorQuasiIso sq →
    IsIso (Algebra.CotangentComplex.mapDerived sq))
