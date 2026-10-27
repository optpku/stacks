/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.AlgebraicGeometry.AlgebraicStack.Sites.DerivedComparison
public import stacks_project.Chap96.Lemma_96_12_3_Pullback

@[expose] public section

open CategoryTheory CategoryTheory.Limits

noncomputable section

universe z uC vC w

namespace AlgebraicGeometry.AlgebraicStack

variable {C D : Type uC} [Category.{vC} C] [Category.{vC} D]

/-- Derived module inverse image along a continuous functor and a coefficient
morphism of ring sheaves. -/
abbrev derivedCoefficientInverseImage
    (J : GrothendieckTopology C) (K : GrothendieckTopology D)
    (f : C ⥤ D) [f.IsContinuous J K]
    {S₀ : Sheaf J RingCat.{w}} {R : Sheaf K RingCat.{w}}
    (α : S₀ ⟶ (f.sheafPushforwardContinuous RingCat.{w} J K).obj R)
    [PreservesFiniteLimits (SheafOfModules.pushforward.{z} α)]
    [PreservesFiniteColimits (SheafOfModules.pushforward.{z} α)]
    [UnivLE.{max uC vC, z}] :
    RingedSite.Hom.ModuleDerived.{z} (RingedSite.ofRingSheaf K R) ⥤
      RingedSite.Hom.ModuleDerived.{z} (RingedSite.ofRingSheaf J S₀) :=
  (ExactFunctor.of (SheafOfModules.pushforward.{z} α)).mapDerivedCategory

end AlgebraicGeometry.AlgebraicStack
