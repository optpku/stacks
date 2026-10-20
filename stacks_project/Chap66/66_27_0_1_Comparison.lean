module

public import Mathlib.CategoryTheory.Comma.Over.Basic
public import Mathlib.CategoryTheory.Sites.Over
public import ReasLib.CategoryTheory.Sites.MorphismOfSites
public import stacks_project.Chap66.Lemma_66_16_4_Etale
public import stacks_project.Chap66.Lemma_66_18_3_Site
public import stacks_project.Chap66.Lemma_66_18_12_Restriction

public import ReasLib.AlgebraicGeometry.AlgebraicSpace.EtaleSite.Localization

@[expose] public section

open CategoryTheory

universe u

/- Étale localization identifies the spaces-étale category with its slice at an étale object. -/
#check (AlgebraicGeometry.AlgebraicSpace.spacesEtaleLocalizationEquivalence :
    ∀ {S : AlgebraicGeometry.Scheme.{u}}
      {X Y : AlgebraicGeometry.AlgebraicSpace S} (f : X ⟶ Y)
      [AlgebraicGeometry.AlgebraicSpace.Etale f],
      AlgebraicGeometry.AlgebraicSpace.spacesEtaleSite X ≌
        CategoryTheory.Over (AlgebraicGeometry.AlgebraicSpace.spacesEtaleSite.mk f))
