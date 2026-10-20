/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.AlgebraicGeometry.Scheme.Sites.Etale.Cohomology.DirectImage.NormalizedInverseSystem

/-!
# Higher direct images on inverse systems of schemes

The ordinary-preorder interface uses equalizers of reflexive transitions, while
the raw diagram retains the original pulled-back higher direct images.
-/

@[expose] public section

open CategoryTheory
open CategoryTheory.Limits
open AlgebraicGeometry AlgebraicGeometry.Scheme
open CategoryTheory.Sheaf

noncomputable section

universe u

namespace AlgebraicGeometry.Scheme.Etale

variable {I : Type u} [Preorder I] [Nonempty I] [IsDirected I (· ≤ ·)]
variable (DX DS : OrderDual I ⥤ Scheme.{u})
variable [∀ i : I, HasSheafify (DX.obj (OrderDual.toDual i)).smallEtaleTopology AddCommGrpCat.{u}]
variable [∀ i : I, HasWeakSheafify (DX.obj (OrderDual.toDual i)).smallEtaleTopology AddCommGrpCat.{u}]
variable [∀ i : I,
    HasInjectiveResolutions
      (Sheaf (DX.obj (OrderDual.toDual i)).smallEtaleTopology AddCommGrpCat.{u})]
variable [∀ i : I, HasSheafify (DS.obj (OrderDual.toDual i)).smallEtaleTopology AddCommGrpCat.{u}]
variable [∀ i : I, HasWeakSheafify (DS.obj (OrderDual.toDual i)).smallEtaleTopology AddCommGrpCat.{u}]
variable [∀ {T U : Scheme.{u}} (f : U ⟶ T)
    (G : T.Etaleᵒᵖ ⥤ AddCommGrpCat.{u}),
    (smallEtalePullback f).op.HasLeftKanExtension G]
variable [∀ {T U : Scheme.{u}} (f : U ⟶ T),
    ((smallEtalePullback f).sheafPushforwardContinuous AddCommGrpCat.{u}
      T.smallEtaleTopology U.smallEtaleTopology).IsRightAdjoint]
variable (g : ∀ i : I, DX.obj (OrderDual.toDual i) ⟶ DS.obj (OrderDual.toDual i))
variable (hg : ∀ {i j : I} (hij : i ≤ j),
    OrderDualInverseSystem.transitionMap DX hij ≫ g i =
      g j ≫ OrderDualInverseSystem.transitionMap DS hij)
variable (cX : Cone DX) (cS : Cone DS)
variable (gX : cX.pt ⟶ cS.pt)
variable (hgX : ∀ i : I,
    cX.π.app (OrderDual.toDual i) ≫ g i = gX ≫ cS.π.app (OrderDual.toDual i))
variable [HasSheafify cS.pt.smallEtaleTopology AddCommGrpCat.{u}]
variable [HasWeakSheafify cS.pt.smallEtaleTopology AddCommGrpCat.{u}]
variable [HasSheafify cX.pt.smallEtaleTopology AddCommGrpCat.{u}]
variable [HasWeakSheafify cX.pt.smallEtaleTopology AddCommGrpCat.{u}]
variable [HasInjectiveResolutions (Sheaf cX.pt.smallEtaleTopology AddCommGrpCat.{u})]
variable (F : AbelianSheafSystem DX) (p : ℕ)

#check (AlgebraicGeometry.Scheme.Etale.higherDirectImage_pullbackDiagram DX DS g hg cS F p :
  I ⥤ Sheaf cS.pt.smallEtaleTopology AddCommGrpCat.{u})

variable [HasColimit (inverseImageDiagram DX cX F)]
variable [HasColimit (higherDirectImage_pullbackDiagram DX DS g hg cS F p)]

#check (AlgebraicGeometry.Scheme.Etale.higherDirectImage_pullbackStageMap
  DX DS g cX cS gX hgX F p : ∀ i : I,
    equalizer (HigherDirectImage.InverseSystem.diagonal DX DS g cS F p i)
      (𝟙 (pullbackStageHigherDirectImage DX DS g cS F p i)) ⟶
        schemeHigherDirectImage gX (colimitInverseImage DX cX F) p)

#check (AlgebraicGeometry.Scheme.Etale.higherDirectImage_pullbackComparison
  DX DS g hg cX cS gX hgX F p :
    colimit (higherDirectImage_pullbackDiagram DX DS g hg cS F p) ⟶
      schemeHigherDirectImage gX (colimitInverseImage DX cX F) p)

#check (AlgebraicGeometry.Scheme.Etale.higherDirectImage_pullbackComparison_ι
  DX DS g hg cX cS gX hgX F p : ∀ i : I,
    colimit.ι (higherDirectImage_pullbackDiagram DX DS g hg cS F p) i ≫
        higherDirectImage_pullbackComparison DX DS g hg cX cS gX hgX F p =
      higherDirectImage_pullbackStageMap DX DS g cX cS gX hgX F p i)

end AlgebraicGeometry.Scheme.Etale

end
