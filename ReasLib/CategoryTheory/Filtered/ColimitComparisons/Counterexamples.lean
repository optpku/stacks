/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

import Mathlib.Tactic.CrossRefAttribute
public import Mathlib.Algebra.Category.Grp.Colimits
public import Mathlib.CategoryTheory.Limits.Shapes.FunctorToTypes
public import ReasLib.CategoryTheory.Filtered.SpanCocones

/-!
# Counterexamples for weak filtered-colimit comparison properties

These existence statements isolate the sharp failures that remain when the
usual filteredness hypotheses are weakened. The positive comparison API is
owned by `Filtered.ColimitComparisons`; this leaf records the two independent
negative boundaries needed by later applications.
-/

@[expose] public section

open CategoryTheory

universe w v u

noncomputable section

namespace CategoryTheory.Limits

namespace prodComparison.colim

/-- There is a small category with pairwise common successors and two `Type`-valued diagrams
whose binary-product colimit comparison is not bijective. -/
@[stacks 09WQ "binary-product colimit counterexample"]
theorem exists_not_bijective :
    ∃ (J : Type u) (_ : Category.{v} J) (_ : Small.{w} J)
      (_ : ∀ i j : J, ∃ k : J, Nonempty (i ⟶ k) ∧ Nonempty (j ⟶ k))
      (F G : J ⥤ Type w),
        ¬ Function.Bijective (prodComparison colim F G) := sorry
/- Proof strategy: take `J` to be `WalkingParallelPair`, whose objects have common successors,
and choose finite diagrams whose separate coequalizer relations identify coordinates
independently while the product diagram only generates simultaneous identifications. -/

end prodComparison.colim

end CategoryTheory.Limits

namespace AddCommGrpCat.colim

open CategoryTheory.Limits

/-- There is a category with commuting span cocones and an objectwise injective natural
transformation of `AddCommGrpCat`-valued diagrams whose colimit map is not injective. -/
@[stacks 09WT "abelian-group colimit monomorphism counterexample"]
theorem exists_map_not_injective :
    ∃ (J : Type) (_ : Category J) (_ : HasSpanCocones J)
      (M N : J ⥤ AddCommGrpCat) (α : M ⟶ N),
      (∀ j : J, Function.Injective (α.app j)) ∧
        ¬ Function.Injective (colim.map α) := sorry
/- Proof strategy: use the one-object groupoid of `Multiplicative (ZMod 2)`, trivial and shear
actions on finite abelian groups, and an objectwise injective map whose induced colimit map is
zero. -/

end AddCommGrpCat.colim

end
