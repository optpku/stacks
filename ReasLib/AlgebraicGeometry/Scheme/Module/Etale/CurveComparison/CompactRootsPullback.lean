/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.AlgebraicGeometry.Scheme.Module.Etale.CurveComparison.ExtensionBaseChange
public import ReasLib.AlgebraicGeometry.Scheme.Module.Etale.CurveComparison.NormalizedTraceTransport
public import ReasLib.AlgebraicGeometry.Scheme.Module.Etale.CurveComparison.RootsModuleSheaf

@[expose] public section
open CategoryTheory CategoryTheory.Limits CategoryTheory.Abelian
open AlgebraicGeometry AlgebraicGeometry.Scheme AlgebraicGeometry.Scheme.AssociatedModule
noncomputable section
universe u

namespace ActualCompactRootsPullback
variable {U U' C D : Scheme.{u}}
variable (j : U ⟶ C) (j' : U' ⟶ D) (g : U' ⟶ U) (f : D ⟶ C)
variable [IsOpenImmersion j] [IsOpenImmersion j']
variable (hcart : IsPullback g j' j f)
variable [HasSheafify C.smallEtaleTopology AddCommGrpCat.{u + 1}]
variable [HasSheafify D.smallEtaleTopology AddCommGrpCat.{u + 1}]
variable [HasSheafify U.smallEtaleTopology AddCommGrpCat.{u + 1}]
variable [HasSheafify U'.smallEtaleTopology AddCommGrpCat.{u + 1}]
variable [HasExt.{u + 1} (Sheaf C.smallEtaleTopology AddCommGrpCat.{u + 1})]
variable [HasExt.{u + 1} (Sheaf D.smallEtaleTopology AddCommGrpCat.{u + 1})]
variable [∀ F : U.Etaleᵒᵖ ⥤ AddCommGrpCat.{u + 1}, (etaleRestriction j).op.HasLeftKanExtension F]
variable [∀ F : U'.Etaleᵒᵖ ⥤ AddCommGrpCat.{u + 1}, (etaleRestriction j').op.HasLeftKanExtension F]
variable [∀ F : C.Etaleᵒᵖ ⥤ AddCommGrpCat.{u + 1}, (smallEtalePullback f).op.HasLeftKanExtension F]
variable [∀ F : U.Etaleᵒᵖ ⥤ AddCommGrpCat.{u + 1}, (smallEtalePullback g).op.HasLeftKanExtension F]
variable (n : ℕ)

/-- The compact roots coefficient pulls back by the actual extension mate
and the map on units/Kummer kernels induced by the interior morphism. -/
def coefficientMap :
    (ActualCompactificationChange.pullbackFunctor f).obj
      ((etaleExtensionByZero j AddCommGrpCat.{u + 1}).obj
        (ActualRootsModule.additiveSheaf U n)) ⟶
    (etaleExtensionByZero j' AddCommGrpCat.{u + 1}).obj
      (ActualRootsModule.additiveSheaf U' n) :=
  (ActualExtensionBaseChange.extensionIso j j' g f hcart AddCommGrpCat.{u + 1}).hom.app
      (ActualRootsModule.additiveSheaf U n) ≫
    (etaleExtensionByZero j' AddCommGrpCat.{u + 1}).map
      (ActualEtaleRootsPullback.rootsOfUnityAddSheafPullbackHom g n)

/-- Compact roots pullback uses exact Ext pullback and the integer-sheaf
normalization, before applying the specified coefficient map. -/
def map (i : ℕ) :
    ((etaleExtensionByZero j AddCommGrpCat.{u + 1}).obj (ActualRootsModule.additiveSheaf U n)).H i →+
    ((etaleExtensionByZero j' AddCommGrpCat.{u + 1}).obj (ActualRootsModule.additiveSheaf U' n)).H i where
  toFun x := Sheaf.H.map (coefficientMap j j' g f hcart n) i
    ((Ext.mk₀ (ActualEtaleRootsPullback.constantAddSheafPullbackIso f).inv).comp
      (x.mapExactFunctor (ActualCompactificationChange.pullbackFunctor f)) (zero_add i))
  map_zero' := sorry
  map_add' := sorry

end ActualCompactRootsPullback

namespace ActualNormalizedTraceTransport
variable {k : Type u} [Field k] [IsAlgClosed k]
variable (C D : SchemeOverField k)
variable [Curve C] [Smooth C.hom] [Projective C.hom]
variable [Curve D] [Smooth D.hom] [Projective D.hom]
variable {U U' : Scheme.{u}}
variable (j : U ⟶ C.left) (j' : U' ⟶ D.left)
variable [IsOpenImmersion j] [IsOpenImmersion j']
variable (eU : U' ≅ U) (eC : D.left ≅ C.left)
variable (hcart : IsPullback eU.hom j' j eC.hom)
variable [HasSheafify C.left.smallEtaleTopology AddCommGrpCat.{u + 1}]
variable [HasSheafify D.left.smallEtaleTopology AddCommGrpCat.{u + 1}]
variable [HasSheafify U.smallEtaleTopology AddCommGrpCat.{u + 1}]
variable [HasSheafify U'.smallEtaleTopology AddCommGrpCat.{u + 1}]
variable [HasExt.{u + 1} (Sheaf C.left.smallEtaleTopology AddCommGrpCat.{u + 1})]
variable [HasExt.{u + 1} (Sheaf D.left.smallEtaleTopology AddCommGrpCat.{u + 1})]
variable [∀ F : U.Etaleᵒᵖ ⥤ AddCommGrpCat.{u + 1}, (etaleRestriction j).op.HasLeftKanExtension F]
variable [∀ F : U'.Etaleᵒᵖ ⥤ AddCommGrpCat.{u + 1}, (etaleRestriction j').op.HasLeftKanExtension F]
variable [∀ F : C.left.Etaleᵒᵖ ⥤ AddCommGrpCat.{u + 1}, (smallEtalePullback eC.hom).op.HasLeftKanExtension F]
variable [∀ F : U.Etaleᵒᵖ ⥤ AddCommGrpCat.{u + 1}, (smallEtalePullback eU.hom).op.HasLeftKanExtension F]

/-- Normalized compact trace is invariant under the specified isomorphism
of pairs, including the semilinear Galois squares. The action map is the
geometric roots pullback above, independent of any character comparison. -/
theorem compact_semilinear (n : ℕ) (hpos : 0 < n) (hn : IsUnit (n : k))
    (x : ((etaleExtensionByZero j AddCommGrpCat.{u + 1}).obj (ActualRootsModule.additiveSheaf U n)).H 2) :
    SchemeOverField.NormalizedCurveTrace.intrinsicCompactKummerTrace D j' n hpos hn
      (ActualCompactRootsPullback.map j j' eU.hom eC.hom hcart n 2 x) =
    SchemeOverField.NormalizedCurveTrace.intrinsicCompactKummerTrace C j n hpos hn x := sorry

end ActualNormalizedTraceTransport
