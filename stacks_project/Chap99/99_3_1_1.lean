/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

import StacksCheckRecall
public import ReasLib.AlgebraicGeometry.AlgebraicSpace.Module.HomFunctor

public import stacks_project.Chap70.Lemma_70_5_6_GlobalSections
public import stacks_project.Chap70.Lemma_70_7_2_FinitePresentation
public import stacks_project.Chap77.«77_7_1_1_IsomorphismFunctor»

@[expose] public section

open CategoryTheory AlgebraicGeometry AlgebraicGeometry.AlgebraicSpace Opposite

universe u

/- 99.3.1.1: The Hom functor sends a scheme `T` over `B` to the type of
`𝒪_{X_T}`-module morphisms `F_T ⟶ G_T`, where `X_T = X ×_B T` and the modules
are pulled back along `X_T ⟶ X`. -/
@[stacks 08JU] #check ((fun {S} {X B} f F G _ _ => AlgebraicGeometry.AlgebraicSpace.Modules.homFunctor f F G) :
  ∀ {S : Scheme.{u}} {X B : AlgebraicSpace S} (f : X ⟶ B)
    (F G : X.Modules) [F.IsQuasicoherent] [G.IsQuasicoherent],
    (SchemeOver B)ᵒᵖ ⥤ Type (u + 1))

#check ((fun {S} {X B} f F G _ _ σ => AlgebraicGeometry.AlgebraicSpace.Modules.homFunctor_obj f F G σ) :
  ∀ {S : Scheme.{u}} {X B : AlgebraicSpace S} (f : X ⟶ B)
    (F G : X.Modules) [F.IsQuasicoherent] [G.IsQuasicoherent] (σ : SchemeOver B),
    (AlgebraicGeometry.AlgebraicSpace.Modules.homFunctor f F G).obj (op σ) =
      (AlgebraicGeometry.AlgebraicSpace.Modules.baseChangeModule f σ.hom F ⟶
        AlgebraicGeometry.AlgebraicSpace.Modules.baseChangeModule f σ.hom G))
