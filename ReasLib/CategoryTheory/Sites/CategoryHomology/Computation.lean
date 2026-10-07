module

public import ReasLib.CategoryTheory.Sites.CategoryHomology.Bar.DeltaFunctor
public import ReasLib.CategoryTheory.Sites.CategoryHomology.Derived
public import Mathlib.CategoryTheory.Comma.Arrow
import Mathlib.Tactic.CrossRefAttribute

/-!
# Computation of category homology by the bar complex

The explicit composable-arrow bar complex computes the canonical left-derived colimit category
homology.  The comparison is deliberately proposition-valued until a concrete comparison map is
needed by a downstream construction.
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits

noncomputable section

universe u v u' v' w

namespace CategoryTheory.CategoryHomology

variable {C : Type u} [Category.{v} C]
variable [UnivLE.{max u v, w}]
variable [HasColimitsOfShape Cᵒᵖ AddCommGrpCat.{w}]
variable [HasProjectiveResolutions (Cᵒᵖ ⥤ AddCommGrpCat.{w})]

/-- Example 21.39.2: the homology of the explicit bar complex computes category homology. -/
@[stacks 08PG "category homology computed by the bar complex"]
theorem isomorphic_homology_complex
    (ℱ : Cᵒᵖ ⥤ AddCommGrpCat.{w}) (n : ℕ) :
    IsIsomorphic (categoryHomology ℱ n) ((complex ℱ).homology n) := sorry

section Map

variable {C' : Type u'} [Category.{v'} C']
variable [UnivLE.{max u' v', w}]
variable [HasColimitsOfShape C'ᵒᵖ AddCommGrpCat.{w}]
variable [HasProjectiveResolutions (C'ᵒᵖ ⥤ AddCommGrpCat.{w})]

/-- The derived-colimit map and the explicit bar-homology map define isomorphic arrows. -/
@[stacks 08PH "derived category homology map computed by the bar map"]
theorem map_isomorphic_barMap (u : C' ⥤ C)
    [((Functor.whiskeringLeft C'ᵒᵖ Cᵒᵖ
      AddCommGrpCat.{w}).obj u.op).PreservesProjectiveObjects]
    {ℱ : Cᵒᵖ ⥤ AddCommGrpCat.{w}}
    {ℱ' : C'ᵒᵖ ⥤ AddCommGrpCat.{w}}
    (t : ℱ' ⟶ u.op ⋙ ℱ) (n : ℕ) :
    IsIsomorphic (Arrow.mk (CategoryHomology.map u t n))
      (Arrow.mk (Bar.map u t n)) := sorry

end Map

/-- Derived-colimit and bar category homology are isomorphic as coefficient functors. -/
@[stacks 08PG "derived and bar category homology coefficient functor comparison"]
theorem coefficientFunctor_isomorphic_bar (n : ℕ) :
    IsIsomorphic (CategoryHomology.coefficientFunctor (C := C) n)
      (Bar.coefficientFunctor (C := C) n) := sorry

end CategoryTheory.CategoryHomology
