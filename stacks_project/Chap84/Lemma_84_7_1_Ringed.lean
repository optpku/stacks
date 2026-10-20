/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import stacks_project.Chap84.Lemma_84_5_4_Ringed
public import ReasLib.AlgebraicGeometry.AlgebraicSpace.Fppf.Ringed

@[expose] public section

open CategoryTheory CategoryTheory.Limits Opposite AlgebraicGeometry
open AlgebraicGeometry.AlgebraicSpace AlgebraicGeometry.AlgebraicSpace.Etale
open AlgebraicGeometry.AlgebraicSpace.Etale.SmallToBig
open AlgebraicGeometry.AlgebraicSpace.Fppf

noncomputable section

universe u

#check (AlgebraicGeometry.AlgebraicSpace.Fppf.overFppfStructurePresheaf_obj :
  ∀ {S : Scheme.{u}} (X : AlgebraicSpace S) (U : Over X),
    (overFppfStructurePresheaf X).obj (op U) =
      (forget₂ CommRingCat RingCat).obj (globalSectionsRing U.left))

#check (AlgebraicGeometry.AlgebraicSpace.Fppf.epsilonRingedHom_base :
  ∀ {S : Scheme.{u}} (X : AlgebraicSpace S),
    (epsilonRingedHom X).base = 𝟭 (Over X))

#check (AlgebraicGeometry.AlgebraicSpace.Fppf.epsilonRingedHom_structureSheafMap_app :
  ∀ {S : Scheme.{u}} (X : AlgebraicSpace S)
    (U : (Over X)ᵒᵖ),
    (epsilonRingedHom X).structureSheafMap.hom.app U = 𝟙 _)

#check (AlgebraicGeometry.AlgebraicSpace.Fppf.aRingedHom_eq_comp :
  ∀ {S : Scheme.{u}} (X : AlgebraicSpace S),
    aRingedHom X = RingedSite.Hom.comp (epsilonRingedHom X) (Etale.Atlas.etalePiRingedHom X))

end

end
