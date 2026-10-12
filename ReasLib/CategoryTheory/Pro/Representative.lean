/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import ReasLib.CategoryTheory.Pro.Constant
public import ReasLib.CategoryTheory.Pro.HomColimit
public import Mathlib.Tactic.CrossRefAttribute

/-!
# Stage representatives of pro-values

A map from one stage of a pro-system to an object determines a canonical comparison from the
object's covariant Hom functor to the system's Hom-colimit.  This module packages that comparison
and the predicate that it is invertible, giving a stage-level interface to `Pro.HasValue`.
-/

@[expose] public section

open CategoryTheory Limits Opposite
open scoped CategoryTheory

universe uC vC uI vI

namespace CategoryTheory

namespace Pro

variable {C : Type uC} [Category.{vC} C]

/-- A diagram has pro-value `X` when its covariant Hom-colimit functor is corepresented by `X`.
This is the value notion used in Lemma 13.42.2 (0G3A). -/
@[stacks 0G3A]
def HasValue {I : Type uI} [Category.{vI} I] [Small.{vC} I]
    (F : I ⥤ C) (X : C) : Prop :=
  Nonempty ((Pro.homColimit F).CorepresentableBy X)

end Pro

namespace CostructuredArrow

variable {C : Type uC} [Category.{vC} C]
variable {I : Type uI} [Category.{vI} I] [Small.{vC} I]

/-- The canonical map from `Hom(X, -)` to the Hom-colimit of `F` induced by a stage map
`p : F.obj p.left ⟶ X`. -/
noncomputable def homColimitComparison {F : I ⥤ C} {X : C} (p : CostructuredArrow F X) :
    coyoneda.obj (op X) ⟶ Pro.homColimit F :=
  coyonedaEquiv.symm
    ((colimit.ι (F.op ⋙ coyoneda) (op p.left)).app X p.hom)

/-- A stage map represents the pro-value `X` precisely when its canonical Hom-colimit comparison
is an isomorphism. This is the stage-wise interface used by Lemma 13.42.2 (0G3A). -/
@[stacks 0G3A]
noncomputable def IsHomColimitRepresentative {F : I ⥤ C} {X : C}
    (p : CostructuredArrow F X) : Prop :=
  IsIso p.homColimitComparison

/-- The Hom-colimit comparison sends `f : X ⟶ Y` to the colimit class of `p.hom ≫ f`. -/
theorem homColimitComparison_app {F : I ⥤ C} {X : C} (p : CostructuredArrow F X)
    (Y : C) (f : X ⟶ Y) :
    p.homColimitComparison.app Y f =
      (colimit.ι (F.op ⋙ coyoneda) (op p.left)).app Y (p.hom ≫ f) := sorry

/-- The canonical Hom-colimit comparison is invertible exactly when it is bijective at every
test object. -/
theorem isHomColimitRepresentative_iff {F : I ⥤ C} {X : C}
    (p : CostructuredArrow F X) :
    p.IsHomColimitRepresentative ↔
      ∀ Y : C, Function.Bijective (fun f : X ⟶ Y ↦
        (colimit.ι (F.op ⋙ coyoneda) (op p.left)).app Y (p.hom ≫ f)) := sorry

/-- The isomorphism of Hom-colimit functors carried by a representing stage map. -/
noncomputable def homColimitComparisonIso {F : I ⥤ C} {X : C}
    (p : CostructuredArrow F X) (h : p.IsHomColimitRepresentative) :
    coyoneda.obj (op X) ≅ Pro.homColimit F :=
  @asIso _ _ _ _ p.homColimitComparison h

/-- A representing stage map supplies the corresponding pro-value. -/
theorem hasValue {F : I ⥤ C} {X : C} (p : CostructuredArrow F X)
    (h : p.IsHomColimitRepresentative) : Pro.HasValue F X := sorry

end CostructuredArrow

namespace Pro

variable {C : Type uC} [Category.{vC} C]
variable {I : Type uI} [Category.{vI} I] [Small.{vC} I]

/-- A Hom-colimit value of a cofiltered presentation is exactly a constant value of its
canonical pro-object. -/
theorem hasValue_iff_isConstant_lim [LocallySmall.{vC} I] [IsCofiltered I]
    (F : I ⥤ C) (X : C) :
    HasValue F X ↔ IsConstant ((Pro.lim I).obj F) X := sorry

/-- A pro-value is equivalent to a representing map from a single stage of the presentation. -/
theorem hasValue_iff_exists_homColimitRepresentative (F : I ⥤ C) (X : C) :
    HasValue F X ↔ ∃ p : CostructuredArrow F X, p.IsHomColimitRepresentative := sorry

namespace HasValue

/-- A pro-value has a stage map whose Hom-colimit comparison is invertible. -/
theorem exists_homColimitRepresentative {F : I ⥤ C} {X : C}
    (h : HasValue F X) :
    ∃ p : CostructuredArrow F X, p.IsHomColimitRepresentative := sorry

end HasValue

end Pro

end CategoryTheory
