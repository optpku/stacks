/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.RingTheory.Sequence.Koszul.Family
public import ReasLib.Algebra.Homology.Embedding.DownNat
public import ReasLib.Algebra.Homology.DerivedCategory.Perfect

@[expose] public section

noncomputable section

open CategoryTheory
open ComplexShape

universe u

namespace KoszulComplex

variable {R : Type u} [CommRing R]

/-- The derived-category object represented by the finite-family Koszul complex. -/
noncomputable abbrev derivedFamily {r : ℕ} (f : Fin r → R) :
    DerivedCategory (ModuleCat R) :=
  DerivedCategory.Q.obj ((KoszulComplex.family f).extend ComplexShape.embeddingDownNat)

/-- The derived object of a finite-family Koszul complex is perfect. -/
theorem derivedFamily_isPerfect {r : ℕ} (f : Fin r → R) :
    (derivedFamily f).IsPerfect := sorry

end KoszulComplex
