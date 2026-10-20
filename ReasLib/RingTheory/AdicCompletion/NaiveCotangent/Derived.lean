/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.RingTheory.AdicCompletion.NaiveCotangent
public import ReasLib.Algebra.Homology.DerivedCategory.ModuleCat
public import Mathlib.Algebra.Homology.Embedding.Extend

/-!
# Derived completed naive cotangent objects

The completed naive cotangent complex of a finite completed presentation
defines an object in the derived category of modules.
-/

@[expose] public section

open CategoryTheory

noncomputable section

universe u

namespace Algebra.NaiveCotangent.Adic

variable {A B ι : Type u} [CommRing A] [CommRing B] [Algebra A B] [Fintype ι]

/-- The object of `D(B)` represented by the completed naive cotangent complex
`NL_{B/A}^∧` of a finite completed presentation. -/
noncomputable abbrev naiveCotangentObject (I : Ideal A) (P : Presentation A B I ι) :
    DerivedCategory (ModuleCat B) :=
  DerivedCategory.Q.obj ((naiveCotangent I P).extend ComplexShape.embeddingDownNat)

end Algebra.NaiveCotangent.Adic
