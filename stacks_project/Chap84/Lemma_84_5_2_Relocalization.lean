module

public import Mathlib.Algebra.Category.Grp.Abelian
public import Mathlib.CategoryTheory.MorphismProperty.Comma
public import Mathlib.CategoryTheory.Sites.Continuous
public import Mathlib.CategoryTheory.Sites.CoverLifting
public import Mathlib.CategoryTheory.Sites.Over
public import Mathlib.CategoryTheory.Sites.PrecoverageToGrothendieck
public import ReasLib.AlgebraicGeometry.AlgebraicSpace.EtaleSite.Relocalization
public import stacks_project.Chap66.Lemma_66_18_3_Site
public import stacks_project.Chap73.Definition_73_4_1_Precoverage

/-!
# Small-to-big étale relocalization of algebraic spaces

The functor `i_f` sends an étale scheme over an algebraic space `Y` to the same
object of `Over X` along a morphism `f : Y ⟶ X`. Inverse image of abelian
sheaves is precomposition with this functor.
-/

@[expose] public section

open CategoryTheory AlgebraicGeometry

noncomputable section

universe u

namespace AlgebraicGeometry.AlgebraicSpace.Etale.SmallToBig

#check (AlgebraicGeometry.AlgebraicSpace.overEtaleTopology :
  ∀ {S : Scheme.{u}} (X : AlgebraicSpace S), GrothendieckTopology (Over X))

#check (AlgebraicGeometry.AlgebraicSpace.overEtaleTopology_def :
  ∀ {S : Scheme.{u}} (X : AlgebraicSpace S),
    overEtaleTopology X =
      (etalePrecoverage : Precoverage (AlgebraicSpace S)).toGrothendieck.over X)

#check (AlgebraicGeometry.AlgebraicSpace.Etale.SmallToBig.relocalizationFunctor :
  ∀ {S : Scheme.{u}} {X Y : AlgebraicSpace S} (f : Y ⟶ X),
    smallEtaleSite Y ⥤ Over X)

#check (AlgebraicGeometry.AlgebraicSpace.Etale.SmallToBig.relocalizationFunctor_isContinuous :
  ∀ {S : Scheme.{u}} {X Y : AlgebraicSpace S} (f : Y ⟶ X),
    Functor.IsContinuous (relocalizationFunctor f) (smallEtaleTopology Y)
      (overEtaleTopology X))

#check (AlgebraicGeometry.AlgebraicSpace.Etale.SmallToBig.relocalizationFunctor_isCocontinuous :
  ∀ {S : Scheme.{u}} {X Y : AlgebraicSpace S} (f : Y ⟶ X),
    Functor.IsCocontinuous (relocalizationFunctor f) (smallEtaleTopology Y)
      (overEtaleTopology X))

#check (AlgebraicGeometry.AlgebraicSpace.Etale.SmallToBig.inverseImage :
  ∀ {S : Scheme.{u}} {X Y : AlgebraicSpace S} (f : Y ⟶ X),
    Sheaf (overEtaleTopology X) AddCommGrpCat.{u + 1} ⥤
      Sheaf (smallEtaleTopology Y) AddCommGrpCat.{u + 1})

end AlgebraicGeometry.AlgebraicSpace.Etale.SmallToBig

end
