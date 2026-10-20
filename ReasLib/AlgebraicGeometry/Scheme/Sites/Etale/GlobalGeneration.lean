/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import Mathlib.Algebra.Category.Grp.Basic
public import Mathlib.AlgebraicGeometry.Sites.Etale
public import Mathlib.CategoryTheory.Sites.ConstantSheaf

@[expose] public section

open CategoryTheory CategoryTheory.Limits

noncomputable section

universe u

namespace AlgebraicGeometry.Scheme.Etale

variable {X : Scheme.{u}}
variable [HasSheafify X.smallEtaleTopology AddCommGrpCat.{u}] [HasTerminal X.Etale]

/-- An abelian sheaf on the small étale site is globally generated if the counit of
the constant-sheaf adjunction at a terminal object is an epimorphism. -/
abbrev IsGloballyGenerated (F : Sheaf X.smallEtaleTopology AddCommGrpCat.{u}) : Prop :=
  Epi ((constantSheafAdj X.smallEtaleTopology AddCommGrpCat.{u} terminalIsTerminal).counit.app F)

/-- Global generation of an abelian étale sheaf is the epimorphism condition on the
constant-sheaf adjunction counit. -/
theorem isGloballyGenerated_iff (F : Sheaf X.smallEtaleTopology AddCommGrpCat.{u}) :
    IsGloballyGenerated F ↔
      Epi ((constantSheafAdj X.smallEtaleTopology AddCommGrpCat.{u}
          terminalIsTerminal).counit.app F) := Iff.rfl

end AlgebraicGeometry.Scheme.Etale

end
