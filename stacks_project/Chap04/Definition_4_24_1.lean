/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import Mathlib.CategoryTheory.Adjunction.Basic
import StacksCheckRecall

@[expose] public section

namespace CategoryTheory

universe vC uC vD uD

variable {C : Type uC} [Category.{vC} C]
variable {D : Type uD} [Category.{vD} D]
variable {L : C ⥤ D} {R : D ⥤ C} (adj : L ⊣ R)

/- The source-facing need is the notion for fixed functors `u : C ⥤ D` and `v : D ⥤ C` given by
a hom-set equivalence natural in both variables. `Adjunction.CoreHomEquiv` packages that
presentation and `Adjunction.mkOfHomEquiv` converts it, while the Stacks-tagged canonical owner is
`Adjunction`; its `Adjunction.homEquiv` recovers the source family. Recalling the owner keeps
exactly the fixed-functor boundary and exposes both presentations for downstream use without
making the auxiliary construction data a second public notion. -/

/- Definition 4.24.1: for functors `u : C ⥤ D` and `v : D ⥤ C`, `u ⊣ v` says that `u` is a left
adjoint of `v`, equivalently that `v` is a right adjoint to `u`; its hom-set equivalences
`(u.obj X ⟶ Y) ≃ (X ⟶ v.obj Y)` are natural in `X` and `Y`. -/
@[stacks 0037 "adjunction via natural hom-set equivalences"]
#check (adj : Adjunction L R)

end CategoryTheory
