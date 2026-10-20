module

public import Mathlib.CategoryTheory.CatCommSq
public import ReasLib.CategoryTheory.Sites.MorphismOfSites
public import ReasLib.CategoryTheory.Sites.Topos.Continuous
public import stacks_project.Chap66.Lemma_66_18_8_Topos
public import stacks_project.Chap73.Lemma_73_8_8_Big
public import stacks_project.Chap84.Lemma_84_5_2_Relocalization
public import stacks_project.Chap84.Lemma_84_8_4_Big

public import ReasLib.AlgebraicGeometry.AlgebraicSpace.Ph.Comparison

/-! # Compatibility checks for ph and étale comparison morphisms -/

@[expose] public section

open CategoryTheory AlgebraicGeometry AlgebraicGeometry.AlgebraicSpace
open scoped MorphismOfTopoiIn

universe u

#check (AlgebraicGeometry.AlgebraicSpace.Etale.SmallToBig.siteMorphismOfTopoi :
  ∀ {S : Scheme.{u}} (X : AlgebraicSpace S),
    MorphismOfTopoiIn.{u + 1, u + 1, u, u + 1, u + 1}
      (smallEtaleTopology X) (overEtaleTopology X))

#check (AlgebraicGeometry.AlgebraicSpace.PhComparison.bigPhEtaleCommSq :
  ∀ {S : Scheme.{u}} {X Y : AlgebraicSpace S} (f : X ⟶ Y),
    Nonempty (CatCommSq
      (Ph.Big.morphismOfTopoi f).pushforward
      (PhComparison.epsilon X).pushforward
      (PhComparison.epsilon Y).pushforward
      (Etale.Big.morphismOfTopoi f).pushforward))

#check (AlgebraicGeometry.AlgebraicSpace.PhComparison.phSmallEtaleCommSq :
  ∀ {S : Scheme.{u}} {X Y : AlgebraicSpace S} (f : X ⟶ Y),
    Nonempty (CatCommSq
      (Ph.Big.morphismOfTopoi f).pushforward
      (PhComparison.toSmallEtale X).pushforward
      (PhComparison.toSmallEtale Y).pushforward
      (smallEtaleMorphismOfTopoi f).pushforward))
