/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import Mathlib.Algebra.Homology.DerivedCategory.TStructure
public import Mathlib.RingTheory.Noetherian.Defs
public import ReasLib.RingTheory.AdicCompletion.TopologicallyFiniteType
public import ReasLib.RingTheory.AdicCompletion.NaiveCotangent.Derived

/-!
# Derived completed naive cotangent objects

This leaf sends a finite completed presentation's two-term Jacobian complex
`NL_{B/A}^∧` to its object in `D(B)`.
-/

@[expose] public section

universe u

#check (Algebra.NaiveCotangent.Adic.naiveCotangentObject :
  ∀ {A B ι : Type u} [CommRing A] [CommRing B] [Algebra A B] [Fintype ι]
    (I : Ideal A) (P : Algebra.NaiveCotangent.Adic.Presentation A B I ι),
    DerivedCategory (ModuleCat B))
