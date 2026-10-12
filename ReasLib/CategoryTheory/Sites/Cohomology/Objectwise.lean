/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import Mathlib.CategoryTheory.Sites.SheafCohomology.Basic
public import ReasLib.CategoryTheory.Sites.Cohomology.Presheaf
import Mathlib.Tactic.CrossRefAttribute

/-!
# Objectwise sheaf cohomology functors

This leaf packages evaluation of the cohomology presheaf functor at a fixed
object of a site, with object and morphism computation API.
-/

@[expose] public section

noncomputable section

universe z w w' v u

namespace CategoryTheory.Sheaf

open CategoryTheory
open Opposite

variable {C : Type u} [Category.{v} C] {J : GrothendieckTopology C}

/-- The functor sending an abelian sheaf `F` to its `i`th cohomology object over the fixed site
object `X`. -/
@[stacks 03AY "objectwise cohomology functor"]
noncomputable def cohomologyOverObjectFunctor
    (J : GrothendieckTopology C)
    [HasSheafify J AddCommGrpCat.{max w v}]
    [HasExt.{z} (Sheaf J AddCommGrpCat.{max w v})]
    (X : C) (i : ℕ) :
    Sheaf J AddCommGrpCat.{max w v} ⥤ AddCommGrpCat.{z} :=
  cohomologyOverPresheafFunctor J (uliftYoneda.{w}.obj X) i

/-- The degree-`i` cohomology functor evaluated at a fixed site object, without a universe lift on
the representable. -/
@[stacks 03AY "cohomology at a fixed object"]
abbrev cohomologyAtObjectFunctor
    (J : GrothendieckTopology C)
    [HasSheafify J AddCommGrpCat.{v}]
    [HasExt.{w'} (Sheaf J AddCommGrpCat.{v})]
    (X : C) (i : ℕ) :
    Sheaf J AddCommGrpCat.{v} ⥤ AddCommGrpCat.{w'} :=
  cohomologyPresheafFunctor.{w', v, u} J i ⋙
    (evaluation Cᵒᵖ AddCommGrpCat.{w'}).obj (op X)

/-- Evaluating `cohomologyAtObjectFunctor` gives the usual objectwise cohomology object `H'`. -/
@[simp, stacks 03AY "objectwise cohomology evaluation"]
theorem cohomologyAtObjectFunctor_obj
    (J : GrothendieckTopology C)
    [HasSheafify J AddCommGrpCat.{v}]
    [HasExt.{w'} (Sheaf J AddCommGrpCat.{v})]
    (X : C) (i : ℕ) (F : Sheaf J AddCommGrpCat.{v}) :
    (cohomologyAtObjectFunctor J X i).obj F = F.H' i X := sorry

/-- A sheaf morphism acts on `cohomologyAtObjectFunctor` by the corresponding evaluated
cohomology-presheaf morphism. -/
@[simp, stacks 03AY "objectwise cohomology map evaluation"]
theorem cohomologyAtObjectFunctor_map
    (J : GrothendieckTopology C)
    [HasSheafify J AddCommGrpCat.{v}]
    [HasExt.{w'} (Sheaf J AddCommGrpCat.{v})]
    (X : C) (i : ℕ) {F G : Sheaf J AddCommGrpCat.{v}} (φ : F ⟶ G) :
    (cohomologyAtObjectFunctor J X i).map φ =
      ((cohomologyPresheafFunctor.{w', v, u} J i).map φ).app (op X) := sorry

/-- Objectwise sheaf cohomology with coefficients raised independently of the site universe. -/
@[stacks 03AY "objectwise cohomology with raised coefficients"]
abbrev cohomologyOverObject
    (F : Sheaf J AddCommGrpCat.{max w v})
    [HasSheafify J AddCommGrpCat.{max w v}]
    [HasExt.{z} (Sheaf J AddCommGrpCat.{max w v})]
    (X : C) (i : ℕ) : AddCommGrpCat.{z} :=
  (cohomologyOverObjectFunctor J X i).obj F

/-- Evaluating `cohomologyOverObjectFunctor` at a sheaf gives the standard objectwise sheaf
cohomology object `H^i(X, F)`. -/
@[simp, stacks 03AY "raised objectwise cohomology evaluation"]
theorem cohomologyOverObjectFunctor_obj
    [HasSheafify J AddCommGrpCat.{max w v}]
    [HasExt.{z} (Sheaf J AddCommGrpCat.{max w v})]
    (X : C) (i : ℕ) (F : Sheaf J AddCommGrpCat.{max w v}) :
    (cohomologyOverObjectFunctor J X i).obj F =
      (cohomologyOverPresheafFunctor J (uliftYoneda.{w}.obj X) i).obj F := sorry

/-- The map of `cohomologyOverObjectFunctor` induced by a sheaf morphism is the corresponding
component of the cohomology presheaf map. -/
@[simp, stacks 03AY "raised objectwise cohomology map evaluation"]
theorem cohomologyOverObjectFunctor_map
    [HasSheafify J AddCommGrpCat.{max w v}]
    [HasExt.{z} (Sheaf J AddCommGrpCat.{max w v})]
    (X : C) (i : ℕ) {F G : Sheaf J AddCommGrpCat.{max w v}} (φ : F ⟶ G) :
    (cohomologyOverObjectFunctor J X i).map φ =
      ((uliftCohomologyPresheafFunctor J i).map φ).app (op X) := sorry

/-- In the unraised coefficient universe, cohomology over the raised representable agrees with
mathlib's standard objectwise sheaf cohomology. -/
@[stacks 03AY "objectwise cohomology compatibility with H'"]
theorem cohomologyOverObjectFunctor_obj_isomorphic_H'
    [HasSheafify J AddCommGrpCat.{v}]
    [HasExt.{z} (Sheaf J AddCommGrpCat.{v})]
    (X : C) (i : ℕ) (F : Sheaf J AddCommGrpCat.{v}) :
    IsIsomorphic
      ((cohomologyOverObjectFunctor.{z, 0, v, u} J X i).obj F)
      (CategoryTheory.Sheaf.H' F i X) := sorry

end CategoryTheory.Sheaf
