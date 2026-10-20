/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.AlgebraicGeometry.Scheme.Sites.Proetale.Pushforward
public import ReasLib.AlgebraicGeometry.Scheme.Sites.Proetale.Injective
public import ReasLib.CategoryTheory.Sites.Over.Derived.BaseChange
public import Mathlib.CategoryTheory.IsomorphismClasses

/-!
# Unbounded derived pro-étale pushforwards

K-injective total right-derived direct images of abelian sheaves on pro-étale
sites, and their compatibility with restriction and relocalization.
-/

@[expose] public section

open AlgebraicGeometry AlgebraicGeometry.Scheme
open CategoryTheory CategoryTheory.Limits
open CategoryTheory.GrothendieckTopology

noncomputable section

universe u

namespace AlgebraicGeometry.Scheme.ProEt

variable {S T : Scheme.{u}} (f : T ⟶ S)

/-- Unbounded derived direct image along the morphism of small pro-étale sites
induced by `f`. -/
abbrev smallDerivedPushforward :
    DerivedCategory (Sheaf (topology T) AddCommGrpCat.{u + 1}) ⥤
      DerivedCategory (Sheaf (topology S) AddCommGrpCat.{u + 1}) :=
  Adjunction.Derived.KInjective.right (smallPushforward f)

/-- Unbounded derived direct image along the morphism of big pro-étale slice
sites induced by `f`. -/
abbrev bigDerivedPushforward
    [HasSheafify (proetaleTopology.over S) AddCommGrpCat.{u + 1}]
    [HasSheafify (proetaleTopology.over T) AddCommGrpCat.{u + 1}]
    [∀ P : (Over T)ᵒᵖ ⥤ AddCommGrpCat.{u + 1},
      (Over.map f).op.HasPointwiseRightKanExtension P] :
    DerivedCategory (Sheaf (proetaleTopology.over T) AddCommGrpCat.{u + 1}) ⥤
      DerivedCategory (Sheaf (proetaleTopology.over S) AddCommGrpCat.{u + 1}) :=
  Derived.Over.pushforward proetaleTopology f

/-- For a cartesian square of schemes, relocalization of the big derived direct
image is isomorphic to the small derived direct image of the relocalization. -/
theorem iInverseImage_bigDerivedPushforward
    {S T S' T' : Scheme.{u}} (f : T ⟶ S) (g : S' ⟶ S) (f' : T' ⟶ S') (g' : T' ⟶ T)
    (sq : IsPullback g' f' f g)
    [HasSheafify (topology S') AddCommGrpCat.{u + 1}]
    [HasSheafify (topology T') AddCommGrpCat.{u + 1}]
    [HasSheafify (proetaleTopology.over S) AddCommGrpCat.{u + 1}]
    [HasSheafify (proetaleTopology.over T) AddCommGrpCat.{u + 1}]
    [∀ P : (Over T)ᵒᵖ ⥤ AddCommGrpCat.{u + 1},
      (Over.map f).op.HasPointwiseRightKanExtension P]
    (K : DerivedCategory (Sheaf (proetaleTopology.over T) AddCommGrpCat.{u + 1})) :
    IsIsomorphic
      ((iInverseImage g).mapDerivedCategory.obj
        ((bigDerivedPushforward f).obj K))
      ((smallDerivedPushforward f').obj
        ((iInverseImage g').mapDerivedCategory.obj K)) := sorry

/-- Restriction of the big pro-étale derived direct image to the small site is
isomorphic to the small derived direct image of the restriction. -/
theorem restrict_bigDerivedPushforward {S T : Scheme.{u}} (f : T ⟶ S)
    [HasSheafify (topology S) AddCommGrpCat.{u + 1}]
    [HasSheafify (topology T) AddCommGrpCat.{u + 1}]
    [HasSheafify (proetaleTopology.over S) AddCommGrpCat.{u + 1}]
    [HasSheafify (proetaleTopology.over T) AddCommGrpCat.{u + 1}]
    [∀ P : (Over T)ᵒᵖ ⥤ AddCommGrpCat.{u + 1},
      (Over.map f).op.HasPointwiseRightKanExtension P]
    (K : DerivedCategory (Sheaf (proetaleTopology.over T) AddCommGrpCat.{u + 1})) :
    IsIsomorphic
      ((iInverseImage (𝟙 S)).mapDerivedCategory.obj
        ((bigDerivedPushforward f).obj K))
      ((smallDerivedPushforward f).obj
        ((iInverseImage (𝟙 T)).mapDerivedCategory.obj K)) := sorry

end AlgebraicGeometry.Scheme.ProEt
