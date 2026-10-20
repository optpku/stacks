/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.AlgebraicGeometry.AlgebraicSpace.EtaleSite.ExtensionByZero

/-! Compatibility interface for étale extension by zero and its trace. -/

@[expose] public section

open CategoryTheory AlgebraicGeometry

noncomputable section

universe u

namespace AlgebraicGeometry.AlgebraicSpace

variable {S : Scheme.{u}}

/-- The constant sheaf of integers on the small étale site of an algebraic space. -/
abbrev constantIntegerSheaf (X : AlgebraicSpace S) :
    Sheaf (smallEtaleTopology X) AddCommGrpCat.{u + 1} :=
  CategoryTheory.constantIntegerSheaf.{u + 1, u, u + 1} (smallEtaleTopology X)

#check (AlgebraicGeometry.AlgebraicSpace.abelianExtensionByZero :
  ∀ {U X : AlgebraicSpace S} (f : U ⟶ X) [Etale f],
    Sheaf (smallEtaleTopology U) AddCommGrpCat.{u + 1} ⥤
      Sheaf (smallEtaleTopology X) AddCommGrpCat.{u + 1})

#check (AlgebraicGeometry.AlgebraicSpace.traceMap :
  ∀ {U X : AlgebraicSpace S} (f : U ⟶ X) [Etale f],
    (abelianExtensionByZero f).obj (constantIntegerSheaf U) ⟶ constantIntegerSheaf X)

end AlgebraicGeometry.AlgebraicSpace
