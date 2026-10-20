/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.AlgebraicGeometry.AlgebraicSpace.Groupoids.IsoClasses
public import ReasLib.AlgebraicGeometry.AlgebraicStack.Gerbe
public import ReasLib.AlgebraicGeometry.AlgebraicSpace.FppfSheaf
public import ReasLib.CategoryTheory.Fibered.FiberIsoClassPresheaf.GroupoidTarget
public import Mathlib.CategoryTheory.Sites.ConcreteSheafification

/-!
# Sheafification of isomorphism classes of a gerbe

The canonical comparison identifies the fppf sheafification of fiberwise
isomorphism classes of a gerbe with its algebraic-space base.
-/

@[expose] public section

open CategoryTheory AlgebraicGeometry Opposite
open FiberedCategoryOver FiberedCategoryOver.Groupoids
open scoped Bicategory

noncomputable section

universe u

namespace AlgebraicGeometry.AlgebraicStack

/-- The fppf sheafification of the presheaf sending a scheme `U` over `S` to the
isomorphism classes of objects in the fiber of an algebraic stack `X` over `U`. -/
noncomputable def isoClassSheaf {S : Scheme.{u}} (X : GroupoidsOver S)
    [AlgebraicStack X] : (Over S)ᵒᵖ ⥤ Type (u + 1) :=
  (Scheme.fppfTopology.over S).sheafify (Functor.fiberIsoClassPresheaf X.p)

/-- The sheafification `isoClassSheaf X` is an fppf sheaf on `Over S`. -/
theorem isoClassSheaf_isSheaf {S : Scheme.{u}} (X : GroupoidsOver S)
    [AlgebraicStack X] :
    Presheaf.IsSheaf (Scheme.fppfTopology.over S) (isoClassSheaf X) :=
  (Scheme.fppfTopology.over S).sheafify_isSheaf (Functor.fiberIsoClassPresheaf X.p)

/-- The presheaf map induced by a morphism `π : X ⟶ Y.toGroupoids`, sending a
fiberwise isomorphism class of `X` to the corresponding point of `Y`. -/
noncomputable def isoClassComparison {S : Scheme.{u}} {X : GroupoidsOver S}
    [AlgebraicStack X] {Y : AlgebraicSpace S} (π : X ⟶ Y.toGroupoids) :
    Functor.fiberIsoClassPresheaf X.p ⟶
      Y.functorOfPoints ⋙ uliftFunctor.{u + 1, u} :=
  BasedFunctor.fiberIsoClassMap (toBasedFunctor π) ≫
    AlgebraicSpace.isoClassToPoints Y

/-- On a represented fiber class, `isoClassComparison π` applies the fiber functor of
`π` and then universe-lifted Grothendieck evaluation. -/
theorem isoClassComparison_app_mk {S : Scheme.{u}} {X : GroupoidsOver S}
    [AlgebraicStack X] {Y : AlgebraicSpace S} (π : X ⟶ Y.toGroupoids)
    (U : (Over S)ᵒᵖ) (x : X.p.Fiber (unop U)) :
    (isoClassComparison π).app U (Quotient.mk'' x) =
      ULift.up
        (Sets.ofPresheaf.fiberToValue Y.functorOfPoints (unop U)
          ((fiberFunctor π (unop U)).obj x)) :=
  sorry

/-- The sheafified comparison obtained by lifting `isoClassComparison π` along
fppf sheafification. -/
noncomputable def isoClassSheafComparison {S : Scheme.{u}} {X : GroupoidsOver S}
    [AlgebraicStack X] {Y : AlgebraicSpace S} (π : X ⟶ Y.toGroupoids) :
    isoClassSheaf X ⟶ Y.functorOfPoints ⋙ uliftFunctor.{u + 1, u} :=
  (Scheme.fppfTopology.over S).sheafifyLift (isoClassComparison π)
    (AlgebraicSpace.toFppfSheaf_isSheaf S Y)

/-- The sheafification unit followed by `isoClassSheafComparison π` recovers
`isoClassComparison π`. -/
theorem toSheafify_isoClassSheafComparison {S : Scheme.{u}} {X : GroupoidsOver S}
    [AlgebraicStack X] {Y : AlgebraicSpace S} (π : X ⟶ Y.toGroupoids) :
    (Scheme.fppfTopology.over S).toSheafify (Functor.fiberIsoClassPresheaf X.p) ≫
        isoClassSheafComparison π =
      isoClassComparison π :=
  (Scheme.fppfTopology.over S).toSheafify_sheafifyLift (isoClassComparison π)
    (AlgebraicSpace.toFppfSheaf_isSheaf S Y)

/-- For a gerbe over an algebraic space, the canonical comparison identifies the
fppf sheafification of fiberwise isomorphism classes with the functor of points
of the base. -/
instance isoClassSheafComparison_isIso {S : Scheme.{u}} {X : GroupoidsOver S}
    [AlgebraicStack X] {Y : AlgebraicSpace S} (π : X ⟶ Y.toGroupoids)
    [hGerbe : Gerbe π] : IsIso (isoClassSheafComparison π) :=
  sorry

/-- A gerbe algebraic stack has an algebraic-space gerbe presentation whose
canonical comparison identifies its iso-class sheafification with the base. -/
theorem exists_isoClassSheafComparison_isIso {S : Scheme.{u}} (X : GroupoidsOver S)
    [AlgebraicStack X] [IsGerbe X] :
    ∃ (Y : AlgebraicSpace S) (π : X ⟶ Y.toGroupoids),
      Gerbe π ∧ IsIso (isoClassSheafComparison π) := by
  obtain ⟨Y, π, hGerbe⟩ := IsGerbe.spec X
  exact ⟨Y, π, hGerbe, isoClassSheafComparison_isIso π (hGerbe := hGerbe)⟩

end AlgebraicGeometry.AlgebraicStack
