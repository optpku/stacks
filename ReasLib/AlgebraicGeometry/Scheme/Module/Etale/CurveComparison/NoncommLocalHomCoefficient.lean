/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module
public import ReasLib.AlgebraicGeometry.Scheme.Module.Etale.CurveComparison.NoncommLocalHom

@[expose] public section
open CategoryTheory CategoryTheory.Limits Opposite
open AlgebraicGeometry AlgebraicGeometry.Scheme
noncomputable section
universe u

namespace NoncommLocalHomCoefficient
variable {A R : Type (u + 1)} [CommRing A] [Ring R]
variable (h : A →+* R) (hc : ∀ (a : A) (r : R), h a * r = r * h a)
variable (Y : Scheme.{u})
variable [Y.smallEtaleTopology.HasSheafCompose (NoncommLocalHom.modules h)]
variable [Y.smallEtaleTopology.HasSheafCompose
  (ModuleCat.restrictScalars (NoncommLocalHom.opScalarHom h hc))]
variable (F : Sheaf Y.smallEtaleTopology (ModuleCat.{u + 1} R))
variable (J : Sheaf Y.smallEtaleTopology (ModuleCat.{u + 1} A))

/-- Identity on the local natural transformations, with the required scalar law explicit. -/
def sectionIso (U : Y.Etaleᵒᵖ) :
    (ModuleCat.restrictScalars (NoncommLocalHom.opScalarHom h hc)).obj
      ((NoncommLocalHom.obj h hc Y F J).obj.obj U) ≅
        (NoncommLocalHom.underlying h Y F J).obj.obj U :=
  ActualModuleRestriction.restrictionIso (NoncommLocalHom.opScalarHom h hc)
    ((NoncommLocalHom.obj h hc Y F J).obj.obj U)
    ((NoncommLocalHom.underlying h Y F J).obj.obj U) (AddEquiv.refl _)
    (NoncommLocalHom.coefficient_smul h hc Y F J U)

/-- Forgetting the right action recovers the same A-linear internal Hom by identity maps. -/
def underlyingIso :
    (sheafCompose Y.smallEtaleTopology
      (ModuleCat.restrictScalars (NoncommLocalHom.opScalarHom h hc))).obj
        (NoncommLocalHom.obj h hc Y F J) ≅ NoncommLocalHom.underlying h Y F J where
  hom := ObjectProperty.homMk
    { app := fun U ↦ (sectionIso h hc Y F J U).hom
      naturality := sorry }
  inv := ObjectProperty.homMk
    { app := fun U ↦ (sectionIso h hc Y F J U).inv
      naturality := sorry }
  hom_inv_id := sorry
  inv_hom_id := sorry

/-- No choice of a comparison map is hidden in scalar rebundling. -/
theorem sectionIso_hom_apply (U : Y.Etaleᵒᵖ)
    (α : NoncommLocalHom.Carrier h Y F J hc U) :
    (sectionIso h hc Y F J U).hom.hom α = α := rfl

end NoncommLocalHomCoefficient
