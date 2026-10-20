/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.AlgebraicGeometry.AlgebraicSpace.EtaleSite.Koszul
public import stacks_project.Chap69.Definition_69_6_2_ExtensionByZero

/-! Compatibility interface for the integer-module trace and its truncated Koszul complex. -/

@[expose] public section

open CategoryTheory AlgebraicGeometry

noncomputable section

universe u

namespace AlgebraicGeometry.AlgebraicSpace

variable {S : Scheme.{u}}

/-- The underlying ring sheaf of the constant integer ring sheaf. -/
noncomputable abbrev integerRingSheaf (X : AlgebraicSpace S) :
    Sheaf (smallEtaleTopology X) RingCat.{u + 1} :=
  CategoryTheory.Sheaf.ringSheafOfComm.{u + 1, u + 1, u} (constantIntegerRingSheaf X)

#check (AlgebraicGeometry.AlgebraicSpace.traceMapModule :
  ∀ {U X : AlgebraicSpace S} (f : U ⟶ X) [Etale f],
    extensionByZeroInteger f ⟶ SheafOfModules.unit (integerRingSheaf X))

#check (AlgebraicGeometry.AlgebraicSpace.koszulComplex :
  ∀ {U X : AlgebraicSpace S} (f : U ⟶ X) [Etale f] [Surjective f],
    ChainComplex (Sheaf (smallEtaleTopology X) AddCommGrpCat.{u + 1}) ℕ)

end AlgebraicGeometry.AlgebraicSpace
