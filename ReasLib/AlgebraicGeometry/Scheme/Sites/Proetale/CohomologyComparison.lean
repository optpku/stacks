/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import Mathlib.Algebra.Homology.DerivedCategory.ExactFunctor
public import Mathlib.Algebra.Homology.DerivedCategory.HomologySequence
public import Mathlib.CategoryTheory.IsomorphismClasses
public import ReasLib.AlgebraicGeometry.Scheme.Sites.ProEtale.Comparison
public import ReasLib.AlgebraicGeometry.Scheme.Sites.Proetale.Abelian
public import ReasLib.AlgebraicGeometry.Scheme.Sites.Proetale.Injective
public import ReasLib.AlgebraicGeometry.Scheme.ProEtale.DerivedSections

/-!
# Cohomology on big and small pro-étale sites

Derived abelian cohomology on the big pro-étale site agrees with cohomology
on a small pro-étale site after the corresponding inverse image.
-/

@[expose] public section

open AlgebraicGeometry AlgebraicGeometry.Scheme
open CategoryTheory CategoryTheory.Limits

noncomputable section

universe u

namespace AlgebraicGeometry.Scheme.ProEt

/-- The cohomology of the small-to-big inverse image at the identity scheme
agrees with the cohomology on the small pro-étale site. -/
theorem proetaleCohomology_piInverseImage (S : Scheme.{u}) (n : ℤ)
    [HasSheafify (topology S) AddCommGrpCat.{u + 1}]
    [HasSheafify (proetaleTopology.over S) AddCommGrpCat.{u + 1}]
    [IsGrothendieckAbelian (Sheaf (topology S) AddCommGrpCat.{u + 1})]
    [IsGrothendieckAbelian (Sheaf (proetaleTopology.over S) AddCommGrpCat.{u + 1})]
    [∀ P : S.ProEtᵒᵖ ⥤ AddCommGrpCat.{u + 1},
      (ProEt.forget S).op.HasLeftKanExtension P]
    (K : DerivedCategory (Sheaf (topology S) AddCommGrpCat.{u + 1})) :
    IsIsomorphic
      ((DerivedCategory.homologyFunctor AddCommGrpCat.{u + 1} n).obj
        ((siteAbelianSectionsDerived (proetaleTopology.over S) (Over.mk (𝟙 S))).obj
          ((piExact S).mapDerivedCategory.obj K)))
      ((DerivedCategory.homologyFunctor AddCommGrpCat.{u + 1} n).obj
        ((siteAbelianSectionsDerived (topology S) (globalProEt S)).obj K)) := sorry

/-- The cohomology of the small-to-big inverse image at a scheme over the base
agrees with small pro-étale cohomology after base change. -/
theorem proetaleCohomology_smallInverseImage {S T : Scheme.{u}} (f : T ⟶ S) (n : ℤ)
    [HasSheafify (topology S) AddCommGrpCat.{u + 1}]
    [HasSheafify (topology T) AddCommGrpCat.{u + 1}]
    [HasSheafify (proetaleTopology.over S) AddCommGrpCat.{u + 1}]
    [IsGrothendieckAbelian (Sheaf (topology S) AddCommGrpCat.{u + 1})]
    [IsGrothendieckAbelian (Sheaf (topology T) AddCommGrpCat.{u + 1})]
    [IsGrothendieckAbelian (Sheaf (proetaleTopology.over S) AddCommGrpCat.{u + 1})]
    [∀ P : S.ProEtᵒᵖ ⥤ AddCommGrpCat.{u + 1},
      (ProEt.forget S).op.HasLeftKanExtension P]
    [∀ P : S.ProEtᵒᵖ ⥤ AddCommGrpCat.{u + 1},
      (smallProetalePullback f).op.HasLeftKanExtension P]
    (K : DerivedCategory (Sheaf (topology S) AddCommGrpCat.{u + 1})) :
    IsIsomorphic
      ((DerivedCategory.homologyFunctor AddCommGrpCat.{u + 1} n).obj
        ((siteAbelianSectionsDerived (proetaleTopology.over S) (Over.mk f)).obj
          ((piExact S).mapDerivedCategory.obj K)))
      ((DerivedCategory.homologyFunctor AddCommGrpCat.{u + 1} n).obj
        ((siteAbelianSectionsDerived (topology T) (globalProEt T)).obj
          ((smallInverseImage f).mapDerivedCategory.obj K))) := sorry

/-- Big pro-étale cohomology at a scheme over the base agrees with small
pro-étale cohomology after relocalization inverse image. -/
theorem proetaleCohomology_relocalization {S T : Scheme.{u}} (f : T ⟶ S) (n : ℤ)
    [HasSheafify (topology T) AddCommGrpCat.{u + 1}]
    [HasSheafify (proetaleTopology.over S) AddCommGrpCat.{u + 1}]
    [IsGrothendieckAbelian (Sheaf (topology T) AddCommGrpCat.{u + 1})]
    [IsGrothendieckAbelian (Sheaf (proetaleTopology.over S) AddCommGrpCat.{u + 1})]
    (M : DerivedCategory (Sheaf (proetaleTopology.over S) AddCommGrpCat.{u + 1})) :
    IsIsomorphic
      ((DerivedCategory.homologyFunctor AddCommGrpCat.{u + 1} n).obj
        ((siteAbelianSectionsDerived (proetaleTopology.over S) (Over.mk f)).obj M))
      ((DerivedCategory.homologyFunctor AddCommGrpCat.{u + 1} n).obj
        ((siteAbelianSectionsDerived (topology T) (globalProEt T)).obj
          ((iInverseImage f).mapDerivedCategory.obj M))) := sorry

end AlgebraicGeometry.Scheme.ProEt
