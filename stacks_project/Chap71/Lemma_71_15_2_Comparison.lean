module

public import Mathlib.AlgebraicGeometry.Modules.Sheaf
public import Mathlib.AlgebraicGeometry.Restrict
public import Mathlib.CategoryTheory.Abelian.RightDerived
public import Mathlib.Topology.Sheaves.Stalks
public import ReasLib.AlgebraicGeometry.RingedSpace.Module.Definition
public import ReasLib.AlgebraicGeometry.RingedSpace.Module.Sections.Basic
public import ReasLib.AlgebraicGeometry.Scheme.Module.Ample
public import ReasLib.CategoryTheory.Monoidal.Invertible
public import ReasLib.CategoryTheory.Sites.Topos.InternalModule
public import stacks_project.Chap66.Lemma_66_27_1_Hom
public import stacks_project.Chap66.Lemma_66_29_2_Pullback
public import stacks_project.Chap69.«69_3_0_1_HigherDirectImage»
public import stacks_project.Chap69.Lemma_69_11_2_Flat_base_change_BaseChange
public import stacks_project.Chap69.Lemma_69_12_5_Monoidal
public import stacks_project.Chap69.Lemma_69_16_2_ToSpec
public import stacks_project.Chap69.Lemma_69_20_1_Tensor
public import stacks_project.Chap71.Lemma_71_15_2_Fiber
public import ReasLib.AlgebraicGeometry.AlgebraicSpace.Module.Fiber
import StacksCheckRecall

@[expose] public section

open CategoryTheory CategoryTheory.Limits CategoryTheory.MonoidalCategory
open AlgebraicGeometry AlgebraicGeometry.AlgebraicSpace
open Opposite TopologicalSpace
open scoped AlgebraicGeometry

noncomputable section

universe u

-- Local instance justification (defeq pin): `HasInjectiveResolutions` and `higherDirectImage` pin the Abelian-induced `Preadditive`/`HasZeroMorphisms` instances for defeq of `higherDirectImage`.
attribute [local instance 2000] Abelian.toPreadditive Preadditive.preadditiveHasZeroMorphisms

/- Lemma 71.15.2: restriction of modules and the canonical stalk-to-fibre comparison. -/
#check (AlgebraicGeometry.AlgebraicSpace.Modules.moduleOnScheme :
  ∀ {Y : Scheme.{u}} {X : AlgebraicSpace Y}
    (f : X ⟶ ofOver (Over.mk (𝟙 Y))) (y : Y) {T : Over Y},
    (fiber f y ≅ ofOver T) → X.Modules → T.left.Modules)

#check (AlgebraicGeometry.AlgebraicSpace.Modules.pushforwardStalkToFiberCohomology :
  ∀ {Y : Scheme.{u}} {X : AlgebraicSpace Y}
    (f : X ⟶ ofOver (Over.mk (𝟙 Y)))
    [Abelian X.Modules] [Abelian (ofOver (Over.mk (𝟙 Y))).Modules]
    [HasInjectiveResolutions X.Modules] (G : X.Modules) (y : Y) {T : Over Y}
    (e : fiber f y ≅ ofOver T),
    TopCat.Presheaf.stalk (C := AddCommGrpCat.{u})
        (AlgebraicGeometry.AlgebraicSpace.Modules.higherDirectImageOnScheme f G 0).val.presheaf y ⟶
      RingedSpace.moduleGlobalSections
        (AlgebraicGeometry.AlgebraicSpace.Modules.moduleOnScheme f y e G))
