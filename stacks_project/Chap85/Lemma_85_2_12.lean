/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

import StacksCheckRecall
public import ReasLib.Topology.Category.TopCat.DiagramOpens.ConstantTopos

@[expose] public section

open CategoryTheory CategoryTheory.Functor CategoryTheory.Limits Opposite TopologicalSpace TopCat
open scoped Simplicial CategoryTheory.MorphismOfTopoiIn

noncomputable section

universe u

namespace CategoryTheory.SimplicialObject

variable (X : TopCat.{u})
variable [HasSheafify (zariskiTopology (constSpace X)) (Type u)]
variable [∀ F : (zariskiSite (constSpace X))ᵒᵖ ⥤ Type u,
    (constProjection X).op.HasPointwiseRightKanExtension F]

/- Lemma 85.2.12. The constant simplicial space has a continuous and cocontinuous
projection, with constant inverse image, degree-zero lower shriek, and equalizer direct image. -/
@[stacks 09W3] #check (CategoryTheory.SimplicialObject.constMorphism X :
  MorphismOfTopoiIn (Opens.grothendieckTopology X) (zariskiTopology (constSpace X)))

#check (CategoryTheory.SimplicialObject.constProjection_isContinuous X :
  (constProjection X).IsContinuous (zariskiTopology (constSpace X))
    (Opens.grothendieckTopology X))
#check (CategoryTheory.SimplicialObject.constProjection_isCocontinuous X :
  (constProjection X).IsCocontinuous (zariskiTopology (constSpace X))
    (Opens.grothendieckTopology X))

section InverseImage

variable [HasWeakSheafify (zariskiTopology (constSpace X)) (Type u)]
variable [HasWeakSheafify (Opens.grothendieckTopology X) (Type u)]

#check (CategoryTheory.SimplicialObject.constMorphism_inverseImage_iso X :
  (constMorphism X)⁻¹ ≅ (constProjection X).sheafPushforwardContinuous (Type u)
    (zariskiTopology (constSpace X)) (Opens.grothendieckTopology X))
#check (CategoryTheory.SimplicialObject.constMorphism_inverseImage_const X :
  ∀ F : Sheaf (Opens.grothendieckTopology X) (Type u),
    (toCosimplicial X (Type u)).obj ((constMorphism X)⁻¹.obj F) ≅
      (CosimplicialObject.const (Sheaf (Opens.grothendieckTopology X) (Type u))).obj F)

variable [∀ F : (zariskiSite (constSpace X))ᵒᵖ ⥤ Type u,
    (constProjection X).op.HasLeftKanExtension F]

#check (CategoryTheory.SimplicialObject.constLowerShriekToposAdjunction X :
  constLowerShriek X ⊣ (constMorphism X)⁻¹)
#check (CategoryTheory.SimplicialObject.lowerShriekIsoComponentZero X :
  ∀ F : Sheaf (zariskiTopology (constSpace X)) (Type u),
    (constLowerShriek X).obj F ≅ (sheafComponent (constSpace X) 0 (Type u)).obj F)

end InverseImage

#check (CategoryTheory.SimplicialObject.pushforwardFork X :
  ∀ F : Sheaf (zariskiTopology (constSpace X)) (Type u),
    Fork (((toCosimplicial X (Type u)).obj F).δ (0 : Fin 2))
      (((toCosimplicial X (Type u)).obj F).δ (1 : Fin 2)))
#check (CategoryTheory.SimplicialObject.pushforwardFork_isLimit X :
  ∀ F : Sheaf (zariskiTopology (constSpace X)) (Type u), IsLimit (pushforwardFork X F))

end CategoryTheory.SimplicialObject
