/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import Mathlib.CategoryTheory.Functor.TypeValuedFlat

/-!
# Explicit over-category model for a type-valued functor

This module supplies the computational form of Mathlib's equivalence between
the elements of a fiber functor and an over-category in a category of
elements.  It is a low-level companion for calculations of colimits indexed
by that equivalence.
-/

@[expose] public section

open CategoryTheory

universe u v w

namespace CategoryTheory.FunctorToTypes.FromOverFunctor

variable {C : Type u} [Category.{v} C]

open CategoryOfElements in
set_option backward.defeqAttrib.useBackward true in
set_option backward.isDefEq.respectTransparency false in
/-- The explicit equivalence from the category of elements of the fiber of a
type-valued functor at `x` to the over-category of `x` in its category of
elements.  Unlike the opaque Mathlib owner, this companion is available for
definitional calculations of indexing diagrams. -/
def elementsEquivalence
    (F : C ⥤ Type w) {X : C} (x : F.obj X) :
    (FunctorToTypes.fromOverFunctor F x).Elements ≌ Over (F.elementsMk X x) where
  functor.obj u :=
    Over.mk (homMk (F.elementsMk u.fst.left u.snd.1) _ u.fst.hom
      ((FunctorToTypes.mem_fromOverSubfunctor_iff (F := F) (x := x)
        (U := u.fst) u.snd.1).1 u.snd.2))
  functor.map f :=
    Over.homMk (homMk _ _ f.val.left (Subtype.ext_iff.1 f.prop))
  inverse.obj u :=
    Functor.elementsMk _ (Over.mk u.hom.1) ⟨u.left.snd,
      (FunctorToTypes.mem_fromOverSubfunctor_iff (F := F) (x := x)
        (U := Over.mk u.hom.1) u.left.snd).2 (by simpa using u.hom.2)⟩
  inverse.map f :=
    homMk _ _ (Over.homMk f.left.val (Subtype.ext_iff.1 (Over.w f))) (by cat_disch)
  unitIso := Iso.refl _
  counitIso := Iso.refl _
  functor_unitIso_comp X := by simp_all; rfl

end CategoryTheory.FunctorToTypes.FromOverFunctor
