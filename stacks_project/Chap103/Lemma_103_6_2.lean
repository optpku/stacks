/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.AlgebraicGeometry.AlgebraicStack.Module.HigherDirectImage
import StacksCheckRecall
public import Mathlib.CategoryTheory.Abelian.RightDerived
public import ReasLib.AlgebraicGeometry.GroupoidsOver.Etale.DirectImage
public import ReasLib.AlgebraicGeometry.AlgebraicStack.Etale.SmallSections
public import stacks_project.Chap103.Lemma_103_8_3_LiftedCFG
public import stacks_project.Chap96.Lemma_96_12_3_Pullback
public import stacks_project.Chap101.Definition_101_4_1_Separation
public import stacks_project.Chap101.Definition_101_7_2_QuasiCompact

/-!
# Locally quasi-coherent higher direct images on algebraic stacks

Along a quasi-compact and quasi-separated morphism of algebraic stacks, étale
higher direct images of locally quasi-coherent modules remain locally
quasi-coherent.
-/

@[expose] public section

open AlgebraicGeometry CategoryTheory CategoryTheory.ObjectProperty
open AlgebraicGeometry.GroupoidsOver FiberedCategoryOver.Groupoids
open scoped Bicategory

noncomputable section

universe u

namespace AlgebraicGeometry.GroupoidsOver

variable {S : Scheme.{u}}

/-- The size-aware morphism of étale ringed topoi induced by a 1-morphism. -/
abbrev moduleDirectImageToposHom {X Y : GroupoidsOver S} (f : X ⟶ Y)
    [HasSmallCFGTypeSections f] :
    RingedSite.ToposHom (etaleRingedSite X) (etaleRingedSite Y) :=
  etaleRingedToposHom f

/-- Direct image `f_*` of étale `𝒪`-modules along a 1-morphism, on the commutative
étale ringed site, with structure map the inverse of `etaleStructureSheafMap`. -/
abbrev moduleDirectImage {X Y : GroupoidsOver S} (f : X ⟶ Y)
    [HasSmallCFGTypeSections f] :
    etaleModules X ⥤ etaleModules Y :=
  etaleModuleDirectImage f

end AlgebraicGeometry.GroupoidsOver

/- Lemma 103.6.2: étale higher direct images of locally quasi-coherent modules
along a quasi-compact and quasi-separated morphism of algebraic stacks are
locally quasi-coherent. -/
@[stacks 075Z] #check (AlgebraicGeometry.AlgebraicStack.isLocallyQuasiCoherent_higherDirectImage :
  ∀ {S : Scheme.{u}} {X Y : GroupoidsOver S} [AlgebraicStack X] [AlgebraicStack Y]
    (f : X ⟶ Y) [AlgebraicGeometry.AlgebraicStack.QuasiCompact f]
    [AlgebraicGeometry.AlgebraicStack.QuasiSeparated f]
    (F : GroupoidsOver.etaleModules X) [IsLocallyQuasiCoherent F] (i : ℕ),
    IsLocallyQuasiCoherentLift (GroupoidsOver.moduleHigherDirectImage f F i))
