/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.AlgebraicGeometry.AlgebraicSpace.Curve.Category
public import ReasLib.AlgebraicGeometry.AlgebraicSpace.Spaces.Groupoids
public import ReasLib.AlgebraicGeometry.AlgebraicSpace.CohStack.Representable
public import ReasLib.AlgebraicGeometry.AlgebraicSpace.Immersion
public import ReasLib.AlgebraicGeometry.AlgebraicSpace.Pullback

/-!
# The inclusion of families of curves

The full-subcategory inclusion of families of curves into finitely presented,
flat, proper families of algebraic spaces is representable by open and closed
immersions.
-/

@[expose] public section

open CategoryTheory AlgebraicGeometry AlgebraicGeometry.AlgebraicSpace
open AlgebraicGeometry.AlgebraicSpace.Spaces
open AlgebraicGeometry.GroupScheme
open CategoryTheory.Limits
open FiberedCategoryOver
open scoped Bicategory

noncomputable section

universe u

namespace AlgebraicGeometry.AlgebraicSpace.Spaces.Curves

/-- The canonical inclusion of families of curves into finitely presented,
flat, proper families of algebraic spaces, as a morphism of groupoid fibrations. -/
def inclusionHom (S : Scheme.{u}) :
    Curves.toGroupoids S ⟶ FpFlatProperGroupoids.toGroupoids S :=
  Groupoids.ofBasedFunctor
    { toFunctor := Curves.inclusion S
      w := rfl }

/-- The underlying functor of the inclusion of groupoid fibrations is the
full-subcategory inclusion of families of curves. -/
theorem inclusionHom_toFunctor (S : Scheme.{u}) :
    Groupoids.toFunctor (inclusionHom S) = Curves.inclusion S := rfl

/-- The inclusion of families of curves commutes strictly with the projections
to schemes over the base. -/
theorem inclusionHom_comm (S : Scheme.{u}) :
    Groupoids.toFunctor (inclusionHom S) ⋙ pFpFlatProperGroupoids S =
      Curves.p S := rfl

/-- For a finitely presented, flat, proper family of algebraic spaces, there is
a clopen subscheme of the base through which a test morphism factors exactly
when its pullback family has relative dimension at most one. -/
theorem exists_isClopen_relativeDimensionLE (S : Scheme.{u})
    (P : FpFlatProperGroupoids S) :
    ∃ U : ((pFpFlatProperGroupoids S).obj P).left.Opens,
      IsClopen (U : Set ((pFpFlatProperGroupoids S).obj P).left) ∧
        ∀ {T : Over S} (h : T ⟶ (pFpFlatProperGroupoids S).obj P),
          Nonempty (Over.mk h.left ⟶ Over.mk U.ι) ↔
            RelativeDimensionLE (pullback.snd P.obj.obj.obj.hom (ofOverMap h)) 1 :=
  sorry

/-- The canonical inclusion of families of curves into finitely presented,
flat, proper families of algebraic spaces is representable by open and closed
immersions. -/
@[stacks 0D5B]
theorem inclusion_isOpenAndClosedImmersion (S : Scheme.{u}) :
    Classifying.relativelyRepresentableByAlgebraicSpaces (inclusionHom S) ∧
      ∀ ⦃U : Over S⦄ (y : Classifying.slice U ⟶ FpFlatProperGroupoids.toGroupoids S)
        (Fy : AlgebraicSpace S) (fy : Fy ⟶ ofOver U),
        Classifying.RepresentsBaseChange (inclusionHom S) y Fy fy →
          AlgebraicSpace.IsOpenImmersion fy ∧ AlgebraicSpace.IsClosedImmersion fy :=
  sorry

end AlgebraicGeometry.AlgebraicSpace.Spaces.Curves
