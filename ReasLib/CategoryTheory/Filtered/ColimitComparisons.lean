/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

import Mathlib.Tactic.CrossRefAttribute
public import Mathlib.Algebra.Category.Grp.Colimits
public import Mathlib.CategoryTheory.Functor.EpiMono
public import Mathlib.CategoryTheory.Limits.Shapes.FunctorToTypes
public import Mathlib.CategoryTheory.Limits.Types.Products
public import ReasLib.CategoryTheory.Filtered.CommonSuccessors
public import ReasLib.CategoryTheory.Filtered.SpanCocones

/-!
# Colimit comparison maps under weak filteredness hypotheses

This module gives computation and surjectivity APIs for canonical colimit comparison maps under
the weakest object- or span-level hypotheses needed by the corresponding statements.
-/

@[expose] public section

open CategoryTheory

universe w v u

noncomputable section

namespace CategoryTheory.Limits

variable {I : Type u} [Category.{v} I]

namespace prodComparison

/-- The first coordinate of the binary-product comparison on a colimit representative. -/
theorem colim.ι.fst
    [Small.{w} I] (M N : I ⥤ Type w) (k : I) (x : (M ⨯ N).obj k) :
    ((Types.binaryProductIso (colimit M) (colimit N)).hom
      (prodComparison colim M N (colimit.ι (M ⨯ N) k x))).1 =
      colimit.ι M k ((prod.fst : M ⨯ N ⟶ M).app k x) := sorry

/-- The second coordinate of the binary-product comparison on a colimit representative. -/
theorem colim.ι.snd
    [Small.{w} I] (M N : I ⥤ Type w) (k : I) (x : (M ⨯ N).obj k) :
    ((Types.binaryProductIso (colimit M) (colimit N)).hom
      (prodComparison colim M N (colimit.ι (M ⨯ N) k x))).2 =
      colimit.ι N k ((prod.snd : M ⨯ N ⟶ N).app k x) := sorry

/-- Common successors make the binary-product comparison for `Type`-valued colimits
surjective. -/
theorem colim.surjective
    [Small.{w} I] [HasCommonSuccessors I] (M N : I ⥤ Type w) :
    Function.Surjective (prodComparison colim M N) := sorry

/-- Explicit-hypothesis form of surjectivity of the binary-product colimit comparison. -/
@[stacks 09WQ "surjectivity of binary-product colimit comparison"]
theorem colim.surjective_of_commonSuccessors
    [Small.{w} I]
    (hObj : ∀ i j : I, ∃ k : I, Nonempty (i ⟶ k) ∧ Nonempty (j ⟶ k))
    (M N : I ⥤ Type w) :
    Function.Surjective (prodComparison colim M N) := sorry

end prodComparison

end CategoryTheory.Limits

namespace AddCommGrpCat

open CategoryTheory.Limits

variable {I : Type u} [Category.{v} I]
variable [Small.{w} I]

/-- The canonical comparison from the colimit of the underlying sets to the underlying set of
the additive colimit. -/
@[stacks 09WR "underlying-set comparison for additive colimits"]
noncomputable def colimitComparison (M : I ⥤ AddCommGrpCat.{w}) :
    colimit (M ⋙ forget AddCommGrpCat) ⟶
      (forget AddCommGrpCat).obj (colimit M) :=
  colimit.post M (forget AddCommGrpCat)

namespace colimitComparison

variable {M : I ⥤ AddCommGrpCat.{w}}

/-- The additive-colimit comparison agrees with the additive colimit injection on every
diagram stage. -/
@[reassoc (attr := simp)]
theorem ι (i : I) :
    colimit.ι (M ⋙ forget AddCommGrpCat) i ≫ colimitComparison M =
      (forget AddCommGrpCat).map (colimit.ι M i) := sorry

/-- Elementwise computation of the additive-colimit comparison on a stage representative. -/
@[simp]
theorem ι_apply (i : I) (x : M.obj i) :
    colimitComparison M (colimit.ι (M ⋙ forget AddCommGrpCat) i x) =
      colimit.ι M i x := sorry

/-- Naturality of the additive-colimit comparison in the additive diagram. -/
@[reassoc]
theorem naturality {N : I ⥤ AddCommGrpCat.{w}} (α : M ⟶ N) :
    colim.map (Functor.whiskerRight α (forget AddCommGrpCat)) ≫ colimitComparison N =
      colimitComparison M ≫ (forget AddCommGrpCat).map (colim.map α) := sorry

/-- For a nonempty index category with common successors, the canonical map from the colimit of
the underlying sets to the underlying set of the additive colimit is surjective. -/
@[stacks 09WR "surjectivity of the additive colimit comparison"]
theorem surjective
    [Nonempty I] [HasCommonSuccessors I] :
    Function.Surjective (colimitComparison M) := sorry

/-- Explicit-hypothesis form of surjectivity of the set-to-abelian-group colimit comparison. -/
@[stacks 09WR "surjectivity of the set-to-abelian-group colimit comparison"]
theorem surjective_of_commonSuccessors
    (hObj : ∀ i j : I, ∃ k : I, Nonempty (i ⟶ k) ∧ Nonempty (j ⟶ k))
    (hI : Nonempty I) :
    Function.Surjective (colimitComparison M) := sorry

end colimitComparison

end AddCommGrpCat

namespace CategoryTheory.Limits

variable {I : Type u} [Category.{v} I]
variable [Small.{w} I]

/-- If every span in the index category has a commuting cocone, its `Type`-valued colimit
functor preserves monomorphisms. -/
@[stacks 09WT "Type-valued colimits preserve objectwise injectivity"]
instance colim.preservesMonomorphisms_of_hasSpanCocones
    [HasSpanCocones I] :
    (colim : (I ⥤ Type w) ⥤ Type w).PreservesMonomorphisms := sorry

end CategoryTheory.Limits
