/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.AlgebraicGeometry.AlgebraicSpace.Module.SpacesGrothendieck
public import ReasLib.AlgebraicGeometry.AlgebraicSpace.RingedSite.SpacesHom
public import ReasLib.Algebra.Category.ModuleCat.Sheaf.TensorScalarExtension

@[expose] public section

open CategoryTheory AlgebraicGeometry

noncomputable section

universe u

namespace AlgebraicGeometry.AlgebraicSpace

variable {S : Scheme.{u}}

/-- Multiplication in the spaces-étale structure sheaf is commutative. -/
theorem spacesStructureRing_mul_comm {X : AlgebraicSpace S}
    (V : (spacesEtaleSite X)ᵒᵖ)
    (x y : (spacesStructureSheaf X).obj.obj V) : x * y = y * x := by
  let e := Iso.ringCatIsoToRingEquiv
    (asIso (Etale.Big.spacesStructureToGamma V.unop) ≪≫
      Etale.Big.gammaGlobalSectionsIso V.unop.left)
  apply e.injective
  simp only [map_mul]
  exact @mul_comm (globalSectionsRing V.unop.left) _ (e x) (e y)

/-- Geometric inverse image preserves commutativity of the structure-ring multiplication. -/
theorem spacesInverseStructureRing_mul_comm {X Y : AlgebraicSpace S} (f : X ⟶ Y)
    (V : (spacesEtaleSite X)ᵒᵖ)
    (x y : ((spacesRingedToposHom f).toTopos.ringInverseImage.obj
      (spacesRingedSite Y).structureSheaf).obj.obj V) : x * y = y * x := sorry

/-- Pullback of spaces-étale modules is geometric inverse image followed by tensor
extension along the inverse-image structure-sheaf map. -/
def spacesModulePullback {X Y : AlgebraicSpace S} (f : X ⟶ Y) :
    RingedSite.ModuleCat.{u} (spacesRingedSite Y) ⥤
      RingedSite.ModuleCat.{u} (spacesRingedSite X) :=
  (spacesRingedToposHom f).toTopos.moduleInverseImage
      (spacesRingedSite Y).structureSheaf ⋙
    SheafOfModules.TensorScalarExtension.functor (spacesRingedToposHom f).structureMap
      (spacesInverseStructureRing_mul_comm f) spacesStructureRing_mul_comm

end AlgebraicGeometry.AlgebraicSpace
