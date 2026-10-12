/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import Mathlib.RingTheory.Ideal.Quotient.Basic
public import Mathlib.RingTheory.RegularLocalRing.Defs
public import Mathlib.Tactic.CrossRefAttribute
public import ReasLib.RingTheory.CohenMacaulay.Module
public import ReasLib.RingTheory.Completion.LocalRing

@[expose] public section

universe u

namespace IsLocalRing

/-- A complete one-dimensional Noetherian Cohen-Macaulay local ring with embedding dimension two
is a principal quotient of a two-dimensional regular local ring. -/
@[stacks 02EN]
theorem exists_dimTwo_regular_spanSingleton_quotient
    {A : Type u} [CommRing A] [IsCompleteLocalRing A] [IsNoetherianRing A]
    [Module.CohenMacaulay A A] (hdim : ringKrullDim A = 1)
    (hemb : Module.finrank (ResidueField A) (CotangentSpace A) = 2) :
    ∃ (B : Type u) (_ : CommRing B) (_ : IsRegularLocalRing B) (F : B),
      ringKrullDim B = 2 ∧ Nonempty ((B ⧸ Ideal.span {F}) ≃+* A) := sorry

end IsLocalRing
