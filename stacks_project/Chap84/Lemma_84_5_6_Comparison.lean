module

public import Mathlib.CategoryTheory.Adjunction.CompositionIso
public import Mathlib.CategoryTheory.Adjunction.Mates
public import Mathlib.CategoryTheory.MorphismProperty.OverAdjunction
public import ReasLib.CategoryTheory.Adjunction.BaseChange
public import ReasLib.CategoryTheory.Adjunction.Derived.Bounded
public import ReasLib.CategoryTheory.Adjunction.Derived.Unbounded
public import ReasLib.CategoryTheory.DerivedCategory.CohomologyIn.Bounded
public import ReasLib.CategoryTheory.DerivedCategory.Functor.Exact.Bounded.Square
public import ReasLib.CategoryTheory.DerivedCategory.Functor.Exact.Square
public import ReasLib.CategoryTheory.Sites.AbelianSheaf.Torsion
public import ReasLib.CategoryTheory.Sites.Over.Abelian
public import ReasLib.CategoryTheory.Sites.Over.Adjunction
public import stacks_project.Chap65.Lemma_65_7_3_Pullback
public import stacks_project.Chap66.Lemma_66_18_8_Topos
public import stacks_project.Chap66.Lemma_66_18_12_Pushforward
public import stacks_project.Chap66.Lemma_66_19_9_Exact
public import stacks_project.Chap66.Lemma_66_27_1_Hom
public import stacks_project.Chap67.Definition_67_40_1_Proper
public import stacks_project.Chap67.Definition_67_45_2_Integral
public import stacks_project.Chap69.Lemma_69_6_5_Sections
public import stacks_project.Chap73.Lemma_73_4_7_Relocalization
public import stacks_project.Chap84.Lemma_84_5_2_Relocalization
public import stacks_project.Chap84.Lemma_84_5_5_SmallToBig
public import stacks_project.Chap84.Lemma_84_8_4_Big
public import stacks_project.Chap84.Lemma_84_8_4_Comparison

public import ReasLib.AlgebraicGeometry.AlgebraicSpace.EtaleSite.SmallToBig.Pushforward
public import ReasLib.AlgebraicGeometry.AlgebraicSpace.EtaleSite.SmallToBig.Derived

/-!
# Small-to-big étale comparison compatibility

The canonical comparison owners supply the inverse-image square and its
sheaf and derived direct-image mates.
-/

open AlgebraicGeometry AlgebraicGeometry.AlgebraicSpace
open AlgebraicGeometry.AlgebraicSpace.Etale
open CategoryTheory
open scoped MorphismOfTopoiIn

universe u

#check (AlgebraicGeometry.AlgebraicSpace.Etale.SmallToBig.smallBigInverseImageSquare :
  {S : Scheme.{u}} → {X Y : AlgebraicSpace S} → (f : Y ⟶ X) →
    (SmallToBig.siteMorphismOfTopoi X)⁻¹ ⋙ (Big.morphismOfTopoi f)⁻¹ ≅
      (smallEtaleMorphismOfTopoi f)⁻¹ ⋙ (SmallToBig.siteMorphismOfTopoi Y)⁻¹)
