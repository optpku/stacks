/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.AlgebraicGeometry.Scheme.Sites.Zariski.Big
public import ReasLib.AlgebraicGeometry.Scheme.Sites.AssociatedModule.UniverseLift
public import ReasLib.AlgebraicGeometry.RingedSite.Topos.HomOfCocontinuous

@[expose] public section

open CategoryTheory

noncomputable section

universe u

namespace AlgebraicGeometry.Scheme.Zariski.Big

variable {T S : Scheme.{u}}

/-- Postcomposition of schemes over a base leaves their rings of global functions unchanged. -/
def ringedStructureMap (f : T ⟶ S) :
    (map f).op ⋙ (AssociatedModule.bigCommRingedSite .zariski S).structureSheaf.obj ⟶
      (AssociatedModule.bigCommRingedSite .zariski T).structureSheaf.obj where
  app A := 𝟙 _
  naturality := sorry

/-- The structure-ring map of big Zariski postcomposition is the identity at each object. -/
theorem ringedStructureMap_app (f : T ⟶ S) (A : (Over T)ᵒᵖ) :
    (ringedStructureMap f).app A = 𝟙 _ := rfl

/-- A scheme morphism induces a morphism of big Zariski ringed topoi by postcomposition. -/
def ringedMorphism (f : T ⟶ S) :
    RingedSite.ToposHom (AssociatedModule.bigCommRingedSite .zariski T)
      (AssociatedModule.bigCommRingedSite .zariski S) :=
  RingedSite.Cocontinuous.toRingedTopos
    (X := AssociatedModule.bigCommRingedSite .zariski T)
    (Y := AssociatedModule.bigCommRingedSite .zariski S) (map f) (ringedStructureMap f)

end AlgebraicGeometry.Scheme.Zariski.Big
