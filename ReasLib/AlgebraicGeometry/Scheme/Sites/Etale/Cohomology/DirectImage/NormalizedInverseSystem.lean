/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import ReasLib.AlgebraicGeometry.Scheme.Sites.Etale.Cohomology.DirectImage.InverseSystem
public import ReasLib.CategoryTheory.Limits.PreorderNormalization

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

/-- Splitting the reflexive higher-direct-image transitions gives an ordinary preorder diagram. -/
def higherDirectImage_pullbackDiagram :
    I ⥤ Sheaf cS.pt.smallEtaleTopology AddCommGrpCat.{u} :=
  PreorderWithAdjoinedIdentities.normalize
    (HigherDirectImage.InverseSystem.diagram DX DS g hg cS F p)

/-- The normalized stage comparison is the raw comparison restricted to the equalizer
of the reflexive transition and the identity. -/
def higherDirectImage_pullbackStageMap
    [HasColimit (inverseImageDiagram DX cX F)] (i : I) :
    equalizer (HigherDirectImage.InverseSystem.diagonal DX DS g cS F p i)
      (𝟙 (pullbackStageHigherDirectImage DX DS g cS F p i)) ⟶
        schemeHigherDirectImage gX (colimitInverseImage DX cX F) p :=
  equalizer.ι (HigherDirectImage.InverseSystem.diagonal DX DS g cS F p i) (𝟙 _) ≫
    HigherDirectImage.InverseSystem.stageMap DX DS g cX cS gX hgX F p i

/-- Restricting the raw comparison cocone gives the normalized comparison cocone. -/
def higherDirectImage_pullbackCocone
    [HasColimit (inverseImageDiagram DX cX F)] :
    Cocone (higherDirectImage_pullbackDiagram DX DS g hg cS F p) :=
  PreorderWithAdjoinedIdentities.normalizedCocone
    (HigherDirectImage.InverseSystem.diagram DX DS g hg cS F p)
    (HigherDirectImage.InverseSystem.cocone DX DS g hg cX cS gX hgX F p)

variable [HasColimit (inverseImageDiagram DX cX F)]
variable [HasColimit (higherDirectImage_pullbackDiagram DX DS g hg cS F p)]

/-- The normalized higher-direct-image comparison is defined by colimit descent. -/
def higherDirectImage_pullbackComparison :
    colimit (higherDirectImage_pullbackDiagram DX DS g hg cS F p) ⟶
      schemeHigherDirectImage gX (colimitInverseImage DX cX F) p :=
  colimit.desc (higherDirectImage_pullbackDiagram DX DS g hg cS F p)
    (higherDirectImage_pullbackCocone DX DS g hg cX cS gX hgX F p)

/-- The normalized comparison restricts to the normalized stage comparison on each colimit leg. -/
theorem higherDirectImage_pullbackComparison_ι (i : I) :
    colimit.ι (higherDirectImage_pullbackDiagram DX DS g hg cS F p) i ≫
        higherDirectImage_pullbackComparison DX DS g hg cX cS gX hgX F p =
      higherDirectImage_pullbackStageMap DX DS g cX cS gX hgX F p i :=
  colimit.ι_desc (higherDirectImage_pullbackCocone DX DS g hg cX cS gX hgX F p) i

/-- The normalized comparison agrees with the raw comparison through the canonical
isomorphism from normalized to raw colimits. -/
theorem higherDirectImage_pullbackComparison_eq
    [HasColimit (HigherDirectImage.InverseSystem.diagram DX DS g hg cS F p)] :
    higherDirectImage_pullbackComparison DX DS g hg cX cS gX hgX F p =
      (PreorderWithAdjoinedIdentities.colimitIso
        (HigherDirectImage.InverseSystem.diagram DX DS g hg cS F p)).hom ≫
          HigherDirectImage.InverseSystem.comparison DX DS g hg cX cS gX hgX F p := sorry

end AlgebraicGeometry.Scheme.Etale

end

