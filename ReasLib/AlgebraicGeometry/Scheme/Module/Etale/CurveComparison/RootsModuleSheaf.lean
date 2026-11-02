/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.AlgebraicGeometry.Scheme.Module.Etale.CurveComparison.LinearSheafHom
public import ReasLib.AlgebraicGeometry.Scheme.Module.Etale.CurveComparison.NormalizedKummerTrace
public import Mathlib.Algebra.Module.ZMod
public import Mathlib.Algebra.Ring.ULift

@[expose] public section
open CategoryTheory AlgebraicGeometry AlgebraicGeometry.Scheme.AssociatedModule
noncomputable section
universe u

namespace ActualRootsModule
variable (Y : Scheme.{u}) (n : ℕ)
variable [HasSheafify Y.smallEtaleTopology AddCommGrpCat.{u + 1}]

abbrev additiveSheaf := Sheaf.rootsOfUnityAddSheaf (smallCommStructureSheaf .etale Y) n

set_option backward.isDefEq.respectTransparency false in
/-- Roots of unity are killed by n, on the actual kernel sheaf's sections. -/
theorem killed (U : Y.Etaleᵒᵖ) (x : (additiveSheaf Y n).obj.obj U) : n • x = 0 := by
  have h : n • 𝟙 (additiveSheaf Y n) = 0 := by
    apply (cancel_mono
      (CategoryTheory.Limits.kernel.ι
        (Sheaf.unitsNsmul (smallCommStructureSheaf .etale Y) n))).1
    simpa [Sheaf.unitsNsmul, CategoryTheory.Preadditive.nsmul_comp,
      CategoryTheory.Preadditive.comp_nsmul] using
      (CategoryTheory.Limits.kernel.condition
        (Sheaf.unitsNsmul (smallCommStructureSheaf .etale Y) n))
  have h' := congrArg
    (sheafToPresheaf Y.smallEtaleTopology AddCommGrpCat.{u + 1}).map h
  rw [CategoryTheory.Functor.map_nsmul, CategoryTheory.Functor.map_id,
    CategoryTheory.Functor.map_zero] at h'
  simpa using congrArg (fun f ↦ (f.app U).hom x) h'

/-- The canonical Z/n action is integer multiplication modulo n. -/
instance sectionModule (U : Y.Etaleᵒᵖ) :
    Module (ZMod n) ((additiveSheaf Y n).obj.obj U) :=
  AddCommGroup.zmodModule (killed Y n U)

/-- The same roots sections and restriction maps, now as Z/n modules. -/
def presheaf : Y.Etaleᵒᵖ ⥤ ModuleCat.{u + 1} (ZMod n) where
  obj U := ModuleCat.of (ZMod n) ((additiveSheaf Y n).obj.obj U)
  map f := ModuleCat.ofHom (((additiveSheaf Y n).obj.map f).hom.toZModLinearMap n)
  map_id U := by
    ext x
    exact congrArg (fun f ↦ f.hom x) ((additiveSheaf Y n).obj.map_id U)
  map_comp f g := by
    ext x
    exact congrArg (fun h ↦ h.hom x) ((additiveSheaf Y n).obj.map_comp f g)

theorem isSheaf : Presheaf.IsSheaf Y.smallEtaleTopology (presheaf Y n) := by
  apply Presheaf.isSheaf_of_isSheaf_comp Y.smallEtaleTopology (presheaf Y n)
    (forget₂ (ModuleCat.{u + 1} (ZMod n)) AddCommGrpCat.{u + 1})
  exact (additiveSheaf Y n).property

def sheaf : Sheaf Y.smallEtaleTopology (ModuleCat.{u + 1} (ZMod n)) :=
  ⟨presheaf Y n, isSheaf Y n⟩

/-- A universe copy of Z/n for the published finite-coefficient API. -/
abbrev Coeff := ULift.{u + 1} (ZMod n)

/-- Scalar transport uses the specified downwards ring equivalence. -/
instance liftedSectionModule (U : Y.Etaleᵒᵖ) :
    Module (Coeff.{u} n) ((additiveSheaf Y n).obj.obj U) :=
  Module.compHom _ ULift.ringEquiv.toRingHom

def liftedPresheaf : Y.Etaleᵒᵖ ⥤ ModuleCat.{u + 1} (Coeff.{u} n) where
  obj U := ModuleCat.of (Coeff.{u} n) ((additiveSheaf Y n).obj.obj U)
  map f := ModuleCat.ofHom
    { toFun := ((additiveSheaf Y n).obj.map f).hom
      map_add' := ((additiveSheaf Y n).obj.map f).hom.map_add
      map_smul' := by
        intro c x
        exact ZMod.map_smul ((additiveSheaf Y n).obj.map f).hom c.down x }
  map_id U := by
    ext x
    exact congrArg (fun f ↦ f.hom x) ((additiveSheaf Y n).obj.map_id U)
  map_comp f g := by
    ext x
    exact congrArg (fun h ↦ h.hom x) ((additiveSheaf Y n).obj.map_comp f g)

theorem liftedIsSheaf : Presheaf.IsSheaf Y.smallEtaleTopology (liftedPresheaf Y n) := by
  apply Presheaf.isSheaf_of_isSheaf_comp Y.smallEtaleTopology (liftedPresheaf Y n)
    (forget₂ (ModuleCat.{u + 1} (Coeff.{u} n)) AddCommGrpCat.{u + 1})
  exact (additiveSheaf Y n).property

/-- Same roots sheaf with the universe-aligned Z/n action. -/
def liftedSheaf : Sheaf Y.smallEtaleTopology (ModuleCat.{u + 1} (Coeff.{u} n)) :=
  ⟨liftedPresheaf Y n, liftedIsSheaf Y n⟩

end ActualRootsModule
