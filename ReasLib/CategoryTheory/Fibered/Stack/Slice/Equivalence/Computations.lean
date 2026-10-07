module

public import ReasLib.CategoryTheory.Fibered.Stack.Slice.Equivalence.Construction
public import ReasLib.CategoryTheory.Fibered.Stack.Slice.Presentation.Computations
import Mathlib.Tactic.CrossRefAttribute

/-!
# Computation rules for direct localization

These lemmas expose direct localization and restriction on objects, `1`-morphisms, and
`2`-morphisms, together with the source-facing domain and structural-map projections.
-/

@[expose] public section

universe u v

namespace CategoryTheory

open Bicategory ObjectProperty
open scoped Bicategory

variable {C : Type u} [Category.{v} C]

namespace StackOver.Localization

variable {J : GrothendieckTopology C}

namespace Localized.toStackSlice

/-- Direct localization acts on objects by extension followed by canonical
repackaging in the internal stack slice. -/
@[simp, stacks 04WV "direct localization object computation"]
theorem obj
    {U : C} (hU : Presheaf.IsSheaf J (yoneda.obj U))
    (X : Localized J U) :
    (Localized.toStackSlice hU).obj X =
      (OverSlice.toStackSlice hU).obj ((Extend.functor hU).obj X) := sorry

/-- Direct localization acts on `1`-morphisms by extension followed by canonical
repackaging in the internal stack slice. -/
@[simp, stacks 04WV "direct localization morphism computation"]
theorem map
    {U : C} (hU : Presheaf.IsSheaf J (yoneda.obj U))
    {X Y : Localized J U} (F : X ⟶ Y) :
    (Localized.toStackSlice hU).map F =
      (OverSlice.toStackSlice hU).map ((Extend.functor hU).map F) := sorry

/-- Direct localization acts on `2`-morphisms by extension followed by canonical
repackaging in the internal stack slice. -/
@[simp, stacks 04WV "direct localization two-cell computation"]
theorem map₂
    {U : C} (hU : Presheaf.IsSheaf J (yoneda.obj U))
    {X Y : Localized J U} {F G : X ⟶ Y} (eta : F ⟶ G) :
    (Localized.toStackSlice hU).map₂ eta =
      (OverSlice.toStackSlice hU).map₂ ((Extend.functor hU).map₂ eta) := sorry

/-- The domain stack of direct localization is the stack carried by the
extended ambient-slice object. -/
@[simp, stacks 04WV "direct localization domain projection"]
theorem domain
    {U : C} (hU : Presheaf.IsSheaf J (yoneda.obj U))
    (X : Localized J U) :
    ((Localized.toStackSlice hU).obj X).obj =
      ((Extend.functor hU).obj X).stack := sorry

/-- Construction A leaves the total category of the localized stack unchanged. -/
@[simp, stacks 04WV "direct localization total category"]
theorem domain.total
    {U : C} (hU : Presheaf.IsSheaf J (yoneda.obj U))
    (X : Localized J U) :
    ((Localized.toStackSlice hU).obj X).obj.total = X.total := sorry

/-- The domain projection produced by Construction A is the original slice-site
projection followed by `Over.forget U`. Heterogeneous equality hides the endpoint
transport introduced by repackaging the domain stack. -/
@[stacks 04WV "direct localization domain projection to the base"]
theorem domain.p
    {U : C} (hU : Presheaf.IsSheaf J (yoneda.obj U))
    (X : Localized J U) :
    HEq ((Localized.toStackSlice hU).obj X).obj.p
      (X.p ⋙ Over.forget U) := sorry

/-- The structural morphism of direct localization is the canonical morphism
carried by the extended ambient-slice object. -/
@[simp, stacks 04WV "direct localization structural map projection"]
theorem arrow
    {U : C} (hU : Presheaf.IsSheaf J (yoneda.obj U))
    (X : Localized J U) :
    ((Localized.toStackSlice hU).obj X).hom =
      OverSlice.hom hU ((Extend.functor hU).obj X) := sorry

/-- The total functor underlying the structural morphism produced by Construction A
is the original projection to the slice category. Heterogeneous equality records only
the endpoint repackaging. -/
@[stacks 04WV "direct localization structural total functor"]
theorem arrow.toFunctor
    {U : C} (hU : Presheaf.IsSheaf J (yoneda.obj U))
    (X : Localized J U) :
    HEq (StackOver.Hom.toFunctor
      ((Localized.toStackSlice hU).obj X).hom) X.p := sorry

end Localized.toStackSlice

namespace StackSlice.toLocalized

/-- Direct restriction acts on objects by forgetting to the ambient slice and
then applying restriction to the slice site. -/
@[simp, stacks 04WV "direct restriction object computation"]
theorem obj
    {U : C} (hU : Presheaf.IsSheaf J (yoneda.obj U))
    (X : StackSlice J U hU) :
    (StackSlice.toLocalized hU).obj X =
      (Restrict.functor hU.isSeparated).obj
        ((StackSlice.toOverSlice hU).obj X) := sorry

/-- Construction B retains the total category of the domain stack. -/
@[simp, stacks 04WV "direct restriction total category"]
theorem obj.total
    {U : C} (hU : Presheaf.IsSheaf J (yoneda.obj U))
    (X : StackSlice J U hU) :
    ((StackSlice.toLocalized hU).obj X).total = X.obj.total := sorry

/-- The projection produced by Construction B is the total functor underlying the
structural morphism to the representable stack. Heterogeneous equality suppresses the
canonical identifications of its source and target categories. -/
@[stacks 04WV "direct restriction slice projection"]
theorem obj.p
    {U : C} (hU : Presheaf.IsSheaf J (yoneda.obj U))
    (X : StackSlice J U hU) :
    HEq ((StackSlice.toLocalized hU).obj X).p
      (StackOver.Hom.toFunctor X.hom) := sorry

/-- Direct restriction acts on `1`-morphisms by forgetting to the ambient slice
and then applying restriction to the slice site. -/
@[simp, stacks 04WV "direct restriction morphism computation"]
theorem map
    {U : C} (hU : Presheaf.IsSheaf J (yoneda.obj U))
    {X Y : StackSlice J U hU} (F : X ⟶ Y) :
    (StackSlice.toLocalized hU).map F =
      (Restrict.functor hU.isSeparated).map
        ((StackSlice.toOverSlice hU).map F) := sorry

/-- Direct restriction acts on `2`-morphisms by forgetting to the ambient slice
and then applying restriction to the slice site. -/
@[simp, stacks 04WV "direct restriction two-cell computation"]
theorem map₂
    {U : C} (hU : Presheaf.IsSheaf J (yoneda.obj U))
    {X Y : StackSlice J U hU} {F G : X ⟶ Y} (eta : F ⟶ G) :
    (StackSlice.toLocalized hU).map₂ eta =
      (Restrict.functor hU.isSeparated).map₂
        ((StackSlice.toOverSlice hU).map₂ eta) := sorry

end StackSlice.toLocalized

end StackOver.Localization

end CategoryTheory
