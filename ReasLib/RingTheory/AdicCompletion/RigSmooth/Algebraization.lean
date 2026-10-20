/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import Mathlib.RingTheory.AdicCompletion.Algebra
public import Mathlib.RingTheory.Finiteness.Defs
public import Mathlib.Tactic.CrossRefAttribute
public import ReasLib.RingTheory.Regular.GRing
public import ReasLib.RingTheory.AdicCompletion.RigSmooth

@[expose] public section

universe u

namespace Algebra.RigSmooth

/-- A rig-smooth algebra over a Noetherian G-ring is isomorphic as an
`A`-algebra to the completion of a finite type `A`-algebra along the extension
of `I`. -/
@[stacks 0GAT]
theorem exists_finiteTypeAlgEquiv
    {A B : Type u} [CommRing A] [IsGRing A] [CommRing B] [Algebra A B]
    (I : Ideal A) [RigSmooth I B] :
    ∃ (C : Type u) (_ : CommRing C) (_ : Algebra A C)
      (_ : Algebra.FiniteType A C),
      Nonempty (AdicCompletion (I.map (algebraMap A C)) C ≃ₐ[A] B) :=
  sorry

/-- A rig-smooth algebra over a Noetherian ring is isomorphic as an
`A`-algebra to the completion of a finite type `A`-algebra along the extension
of `I`. -/
@[stacks 0GAX]
theorem exists_finiteTypeAlgEquiv_of_isNoetherianRing
    {A B : Type u} [CommRing A] [IsNoetherianRing A] [CommRing B] [Algebra A B]
    (I : Ideal A) [RigSmooth I B] :
    ∃ (C : Type u) (_ : CommRing C) (_ : Algebra A C)
      (_ : Algebra.FiniteType A C),
      Nonempty (AdicCompletion (I.map (algebraMap A C)) C ≃ₐ[A] B) :=
  sorry

end Algebra.RigSmooth
