/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
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

/-- Roots of unity are killed by n, on the actual kernel sheaf's sections. -/
theorem killed (U : Y.Etaleᵒᵖ) (x : (additiveSheaf Y n).obj.obj U) : n • x = 0 := sorry

/-- The canonical Z/n action is integer multiplication modulo n. -/
instance sectionModule (U : Y.Etaleᵒᵖ) :
    Module (ZMod n) ((additiveSheaf Y n).obj.obj U) :=
  AddCommGroup.zmodModule (killed Y n U)

/-- The same roots sections and restriction maps, now as Z/n modules. -/
def presheaf : Y.Etaleᵒᵖ ⥤ ModuleCat.{u + 1} (ZMod n) where
  obj U := ModuleCat.of (ZMod n) ((additiveSheaf Y n).obj.obj U)
  map f := ModuleCat.ofHom (((additiveSheaf Y n).obj.map f).hom.toZModLinearMap n)
  map_id := sorry
  map_comp := sorry

theorem isSheaf : Presheaf.IsSheaf Y.smallEtaleTopology (presheaf Y n) := sorry

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
      map_smul' := sorry }
  map_id := sorry
  map_comp := sorry

theorem liftedIsSheaf : Presheaf.IsSheaf Y.smallEtaleTopology (liftedPresheaf Y n) := sorry

/-- Same roots sheaf with the universe-aligned Z/n action. -/
def liftedSheaf : Sheaf Y.smallEtaleTopology (ModuleCat.{u + 1} (Coeff.{u} n)) :=
  ⟨liftedPresheaf Y n, liftedIsSheaf Y n⟩

end ActualRootsModule
