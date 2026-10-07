module

public import ReasLib.CategoryTheory.Filtration.Strict.Abelian
public import ReasLib.CategoryTheory.Filtration.Strict.MonoEpi
public import ReasLib.CategoryTheory.Subobject.Quotient
public import Mathlib.Tactic.CrossRefAttribute

/-!
# Strict Subquotients of Filtered Objects

This file lifts the canonical subquotient API from
`ReasLib.CategoryTheory.Subobject.Quotient` to filtered objects.  The underlying object and map
remain the shared categorical constructions; this layer owns only the induced filtrations and
their strictness comparison.
-/

@[expose] public section

open CategoryTheory Limits

universe v u

noncomputable section

namespace CategoryTheory.FilteredObject

variable {C : Type u} [Category.{v} C] [Abelian C]
namespace Subobject.Subquotient

variable (A : FilteredObject C) {X Y : CategoryTheory.Subobject A.obj}

/-- The subquotient `Y / X`, equipped with the filtration induced from `A / X`. -/
abbrev object (hXY : X ≤ Y) : FilteredObject C :=
  (FilteredObject.Subobject.quotient A X).subobject
    (CategoryTheory.subobjectSubquotientSubobject hXY)

/-- The canonical map `Y ⟶ Y / X` preserves the induced and subquotient filtrations. -/
theorem map_preserves (hXY : X ≤ Y) (i : ℤ) :
    ((object A hXY).filtration i).Factors
      (((A.subobject Y).filtration i).arrow ≫
        CategoryTheory.subobjectToSubquotient hXY) := sorry

/-- The canonical quotient morphism from the induced filtration on `Y` to the filtered
subquotient `Y / X`. -/
def map (hXY : X ≤ Y) :
    A.subobject Y ⟶ object A hXY where
  hom := CategoryTheory.subobjectToSubquotient hXY
  preserves := map_preserves A hXY

/-- Forgetting filtrations identifies the filtered subquotient morphism with the canonical
categorical map `Y ⟶ Y / X`. -/
theorem map_hom (hXY : X ≤ Y) :
    (map A hXY).hom = CategoryTheory.subobjectToSubquotient hXY := sorry

/-- After embedding `Y / X` into `A / X`, its `i`-th filtered stage is the image of the
`i`-th induced stage of `Y` under the ambient quotient map. -/
@[stacks 0129]
theorem stageMap_eq_image (hXY : X ≤ Y) (i : ℤ) :
    (Subobject.map (CategoryTheory.subobjectSubquotientSubobject hXY).arrow).obj
        ((object A hXY).filtration i) =
      imageSubobject
        ((((A.subobject Y).filtration i).arrow ≫ Y.arrow) ≫
          cokernel.π X.arrow) := sorry

/-- The quotient filtration on `Y / X` obtained from the induced filtration on `Y` agrees with
the filtration induced from the ambient quotient `A / X`. -/
@[stacks 0129]
theorem quotientFiltration_eq_induced (hXY : X ≤ Y) :
    (A.subobject Y).filtration.quotient
        (map A hXY).hom =
      (object A hXY).filtration := sorry

/-- The canonical morphism from an induced subobject filtration to its subquotient is strict. -/
@[stacks 0129]
theorem map_strict (hXY : X ≤ Y) :
    Hom.Strict (map A hXY) := sorry

end Subobject.Subquotient

end CategoryTheory.FilteredObject
