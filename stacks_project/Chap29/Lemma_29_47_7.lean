/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

import ReasLib.AlgebraicGeometry.Scheme.Morphism.UniversalHomeomorphism.Seminormalization
import StacksCheckRecall

open CategoryTheory CategoryTheory.Limits

universe u

/- Lemma 29.47.7: every scheme has an initial absolute weak normalization and an initial
seminormalization; the canonical maps from these initial objects characterize absolute weak
normality and seminormality, and every scheme morphism induces unique compatible maps between
the corresponding normalization objects. -/
@[stacks 0EUS] #check
  (AlgebraicGeometry.Scheme.instHasInitialAbsoluteWeakNormalizationOver :
    (X : AlgebraicGeometry.Scheme.{u}) →
      CategoryTheory.Limits.HasInitial
        (AlgebraicGeometry.Scheme.AbsoluteWeakNormalizationOver X))

#check
  (AlgebraicGeometry.Scheme.instHasInitialSeminormalizationOver :
    (X : AlgebraicGeometry.Scheme.{u}) →
      CategoryTheory.Limits.HasInitial (AlgebraicGeometry.Scheme.SeminormalizationOver X))

#check
  (AlgebraicGeometry.Scheme.isIso_initialTo_iff_absolutelyWeaklyNormal :
    (X : AlgebraicGeometry.Scheme.{u}) →
      (Y : AlgebraicGeometry.Scheme.AbsoluteWeakNormalizationOver X) →
        CategoryTheory.IsIso
            (CategoryTheory.Limits.initial.to Y :
              (⊥_ (AlgebraicGeometry.Scheme.AbsoluteWeakNormalizationOver X)) ⟶ Y) ↔
          AlgebraicGeometry.Scheme.AbsolutelyWeaklyNormal Y.1.left)

#check
  (AlgebraicGeometry.Scheme.isIso_initialTo_iff_seminormal :
    (X : AlgebraicGeometry.Scheme.{u}) →
      (Y : AlgebraicGeometry.Scheme.SeminormalizationOver X) →
        CategoryTheory.IsIso
            (CategoryTheory.Limits.initial.to Y :
              (⊥_ (AlgebraicGeometry.Scheme.SeminormalizationOver X)) ⟶ Y) ↔
          AlgebraicGeometry.Scheme.Seminormal Y.1.left)

#check
  (AlgebraicGeometry.Scheme.existsUnique_absoluteWeakNormalizationMap :
    {X X' : AlgebraicGeometry.Scheme.{u}} → (h : X' ⟶ X) →
      ∃! hawn :
          (⊥_ (AlgebraicGeometry.Scheme.AbsoluteWeakNormalizationOver X')).1.left ⟶
            (⊥_ (AlgebraicGeometry.Scheme.AbsoluteWeakNormalizationOver X)).1.left,
        hawn ≫ (⊥_ (AlgebraicGeometry.Scheme.AbsoluteWeakNormalizationOver X)).1.hom =
          (⊥_ (AlgebraicGeometry.Scheme.AbsoluteWeakNormalizationOver X')).1.hom ≫ h)

#check
  (AlgebraicGeometry.Scheme.existsUnique_seminormalizationMap :
    {X X' : AlgebraicGeometry.Scheme.{u}} → (h : X' ⟶ X) →
      ∃! hsn :
          (⊥_ (AlgebraicGeometry.Scheme.SeminormalizationOver X')).1.left ⟶
            (⊥_ (AlgebraicGeometry.Scheme.SeminormalizationOver X)).1.left,
        hsn ≫ (⊥_ (AlgebraicGeometry.Scheme.SeminormalizationOver X)).1.hom =
          (⊥_ (AlgebraicGeometry.Scheme.SeminormalizationOver X')).1.hom ≫ h)

#check
  (CategoryTheory.MorphismProperty.overObj
      (@AlgebraicGeometry.UniversalHomeomorphism :
        CategoryTheory.MorphismProperty AlgebraicGeometry.Scheme.{u}) :
    {X : AlgebraicGeometry.Scheme.{u}} →
      CategoryTheory.ObjectProperty (CategoryTheory.Over X))

#check
  (CategoryTheory.MorphismProperty.overObj_iff :
    ∀ {X : AlgebraicGeometry.Scheme.{u}} (Y : CategoryTheory.Over X),
      CategoryTheory.MorphismProperty.overObj
          (@AlgebraicGeometry.UniversalHomeomorphism :
            CategoryTheory.MorphismProperty AlgebraicGeometry.Scheme.{u}) Y ↔
        AlgebraicGeometry.UniversalHomeomorphism Y.hom)

#check
  (AlgebraicGeometry.Scheme.AbsoluteWeakNormalizationOver :
    AlgebraicGeometry.Scheme.{u} → Type (u + 1))

#check
  (AlgebraicGeometry.Scheme.AbsoluteWeakNormalizationOver.property :
    (X : AlgebraicGeometry.Scheme.{u}) →
      (Y : AlgebraicGeometry.Scheme.AbsoluteWeakNormalizationOver X) →
        AlgebraicGeometry.UniversalHomeomorphism Y.1.hom)

#check
  (AlgebraicGeometry.Scheme.seminormalizationOverProperty :
    (X : AlgebraicGeometry.Scheme.{u}) →
      CategoryTheory.ObjectProperty (CategoryTheory.Over X))

#check
  (AlgebraicGeometry.Scheme.seminormalizationOverProperty_iff :
    (X : AlgebraicGeometry.Scheme.{u}) → (Y : CategoryTheory.Over X) →
      AlgebraicGeometry.Scheme.seminormalizationOverProperty X Y ↔
        AlgebraicGeometry.UniversalHomeomorphism Y.hom ∧
          ∀ y : Y.left,
            CategoryTheory.IsIso (AlgebraicGeometry.Scheme.Hom.residueFieldMap Y.hom y))

#check
  (AlgebraicGeometry.Scheme.SeminormalizationOver :
    AlgebraicGeometry.Scheme.{u} → Type (u + 1))

#check
  (AlgebraicGeometry.Scheme.SeminormalizationOver.property :
    (X : AlgebraicGeometry.Scheme.{u}) →
      (Y : AlgebraicGeometry.Scheme.SeminormalizationOver X) →
        AlgebraicGeometry.UniversalHomeomorphism Y.1.hom ∧
          ∀ y : Y.1.left,
            CategoryTheory.IsIso (AlgebraicGeometry.Scheme.Hom.residueFieldMap Y.1.hom y))
