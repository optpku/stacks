/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import ReasLib.AlgebraicGeometry.Scheme.Sites.Etale.HigherDirectImage.Complex
public import ReasLib.CategoryTheory.Category.PreorderWithAdjoinedIdentities

@[expose] public section

open CategoryTheory
open CategoryTheory.Limits
open CategoryTheory.Functor
open AlgebraicGeometry
open AlgebraicGeometry.Scheme
open CategoryTheory.Sheaf
open ComplexShape

noncomputable section

universe u

namespace AlgebraicGeometry.Scheme.Etale

namespace HigherDirectImage

namespace ComplexSystem

variable {I : Type u} [Preorder I] [Nonempty I] [IsDirected I (· ≤ ·)]
variable (DX DS : OrderDual I ⥤ Scheme.{u})
variable [∀ i : I, HasSheafify (DX.obj (OrderDual.toDual i)).smallEtaleTopology AddCommGrpCat.{u}]
variable [∀ i : I, HasWeakSheafify (DX.obj (OrderDual.toDual i)).smallEtaleTopology AddCommGrpCat.{u}]
variable [∀ i : I, HasSheafify (DS.obj (OrderDual.toDual i)).smallEtaleTopology AddCommGrpCat.{u}]
variable [∀ i : I, HasWeakSheafify (DS.obj (OrderDual.toDual i)).smallEtaleTopology AddCommGrpCat.{u}]
variable [∀ i : I,
    IsGrothendieckAbelian.{u + 1, u + 1, u + 1}
      (Sheaf (DX.obj (OrderDual.toDual i)).smallEtaleTopology AddCommGrpCat.{u})]
variable [∀ i : I,
    IsGrothendieckAbelian.{u + 1, u + 1, u + 1}
      (Sheaf (DS.obj (OrderDual.toDual i)).smallEtaleTopology AddCommGrpCat.{u})]
variable [∀ i : I,
    HasDerivedCategory (Sheaf (DX.obj (OrderDual.toDual i)).smallEtaleTopology AddCommGrpCat.{u})]
variable [∀ i : I,
    HasDerivedCategory (Sheaf (DS.obj (OrderDual.toDual i)).smallEtaleTopology AddCommGrpCat.{u})]
variable [∀ {T U : Scheme.{u}} (f : U ⟶ T)
    (G : T.Etaleᵒᵖ ⥤ AddCommGrpCat.{u}),
    (smallEtalePullback f).op.HasLeftKanExtension G]
variable [∀ {T U : Scheme.{u}} (f : U ⟶ T),
    ((smallEtalePullback f).sheafPushforwardContinuous AddCommGrpCat.{u}
      T.smallEtaleTopology U.smallEtaleTopology).IsRightAdjoint]
variable [∀ {T U : Scheme.{u}} (f : U ⟶ T),
    ((smallEtalePullback f).sheafPushforwardContinuous AddCommGrpCat.{u}
      T.smallEtaleTopology U.smallEtaleTopology).Additive]
variable [∀ {i j : I} (hij : i ≤ j),
    IsAffineHom (OrderDualInverseSystem.transitionMap DX hij)]
variable [∀ {i j : I} (hij : i ≤ j),
    IsAffineHom (OrderDualInverseSystem.transitionMap DS hij)]
variable (g : ∀ i : I, DX.obj (OrderDual.toDual i) ⟶ DS.obj (OrderDual.toDual i))
variable (hg : ∀ {i j : I} (hij : i ≤ j),
    OrderDualInverseSystem.transitionMap DX hij ≫ g i =
      g j ≫ OrderDualInverseSystem.transitionMap DS hij)
variable [∀ i : I, QuasiCompact (g i)]
variable [∀ i : I, QuasiSeparated (g i)]
variable (cX : Cone DX) (cS : Cone DS)
variable (gX : cX.pt ⟶ cS.pt)
variable (hgX : ∀ i : I,
    cX.π.app (OrderDual.toDual i) ≫ g i = gX ≫ cS.π.app (OrderDual.toDual i))
variable [HasSheafify cX.pt.smallEtaleTopology AddCommGrpCat.{u}]
variable [HasWeakSheafify cX.pt.smallEtaleTopology AddCommGrpCat.{u}]
variable [HasSheafify cS.pt.smallEtaleTopology AddCommGrpCat.{u}]
variable [HasWeakSheafify cS.pt.smallEtaleTopology AddCommGrpCat.{u}]
variable [IsGrothendieckAbelian.{u + 1, u + 1, u + 1}
    (Sheaf cX.pt.smallEtaleTopology AddCommGrpCat.{u})]
variable [IsGrothendieckAbelian.{u + 1, u + 1, u + 1}
    (Sheaf cS.pt.smallEtaleTopology AddCommGrpCat.{u})]
variable [HasDerivedCategory (Sheaf cX.pt.smallEtaleTopology AddCommGrpCat.{u})]
variable [HasDerivedCategory (Sheaf cS.pt.smallEtaleTopology AddCommGrpCat.{u})]
variable [((smallEtalePullback gX).sheafPushforwardContinuous AddCommGrpCat.{u}
    cS.pt.smallEtaleTopology cX.pt.smallEtaleTopology).Additive]
variable [Functor.HasRightDerivedFunctor
    (RightDerived.Cochain.toDerived
      ((smallEtalePullback gX).sheafPushforwardContinuous AddCommGrpCat.{u}
        cS.pt.smallEtaleTopology cX.pt.smallEtaleTopology))
    (HomologicalComplex.quasiIso
      (Sheaf cX.pt.smallEtaleTopology AddCommGrpCat.{u}) (up ℤ))]
variable [∀ i : I, Functor.HasRightDerivedFunctor
    (RightDerived.Cochain.toDerived
      ((smallEtalePullback (g i)).sheafPushforwardContinuous AddCommGrpCat.{u}
        (DS.obj (OrderDual.toDual i)).smallEtaleTopology
        (DX.obj (OrderDual.toDual i)).smallEtaleTopology))
    (HomologicalComplex.quasiIso
      (Sheaf (DX.obj (OrderDual.toDual i)).smallEtaleTopology AddCommGrpCat.{u}) (up ℤ))]
variable (F : AbelianSheafComplexSystem DX) (p : ℤ)

/-- The degree-`p` total-derived higher direct image at a stage. -/
def stage (i : I) : Sheaf (DS.obj (OrderDual.toDual i)).smallEtaleTopology AddCommGrpCat.{u} :=
  Complex.value (g i) (F.obj i) p

/-- The stage higher direct image pulled back to the limit base. -/
def pullbackStage (i : I) : Sheaf cS.pt.smallEtaleTopology AddCommGrpCat.{u} :=
  (conePullback DS cS i).obj (stage DX DS g F p i)

/-- The derived base-change transition between two stage higher direct images. -/
def transition {i j : I} (hij : i ≤ j) :
    pullbackStage DX DS g cS F p i ⟶ pullbackStage DX DS g cS F p j :=
  (conePullbackCompIso DS cS hij).inv.app _ ≫
    (conePullback DS cS j).map
      (Complex.baseChange (g i) (g j)
        (OrderDualInverseSystem.transitionMap DX hij)
        (OrderDualInverseSystem.transitionMap DS hij) (hg hij) (F.obj i) p ≫
        Complex.map (g j) (F.transition hij) p)

/-- Derived higher-direct-image transitions compose through every intermediate stage. -/
theorem transition_comp {i j k : I} (hij : i ≤ j) (hjk : j ≤ k) :
    transition DX DS g hg cS F p (le_trans hij hjk) =
      transition DX DS g hg cS F p hij ≫ transition DX DS g hg cS F p hjk := sorry

/-- The identity-adjoined diagram of pulled-back derived higher direct images. -/
def diagram :
    PreorderWithAdjoinedIdentities I ⥤ Sheaf cS.pt.smallEtaleTopology AddCommGrpCat.{u} :=
  PreorderWithAdjoinedIdentities.lift
    (pullbackStage DX DS g cS F p)
    (fun {_ _} hij => transition DX DS g hg cS F p hij)
    (fun {_ _ _} hij hjk => transition_comp DX DS g hg cS F p hij hjk)

/-- The object of the identity-adjoined diagram at an original index. -/
theorem diagram_obj (i : I) :
    (diagram DX DS g hg cS F p).obj i = pullbackStage DX DS g cS F p i := rfl

variable [HasColimit (AbelianSheafComplexSystem.inverseImageComplexDiagram (D := DX) cX F)]

/-- The stage map into the higher direct image of the inverse-image colimit. -/
def stageMap (i : I) :
    pullbackStage DX DS g cS F p i ⟶
      Complex.value gX
        (AbelianSheafComplexSystem.colimitInverseImageComplex cX F) p :=
  Complex.baseChange (g i) gX (cX.π.app (OrderDual.toDual i))
      (cS.π.app (OrderDual.toDual i)) (hgX i) (F.obj i) p ≫
    Complex.map gX
      (AbelianSheafComplexSystem.colimitInverseImageComplex_ι cX F i) p

/-- The stage maps are compatible with all supplied transition maps. -/
theorem stageMap_naturality {i j : I} (hij : i ≤ j) :
    transition DX DS g hg cS F p hij ≫ stageMap DX DS g cX cS gX hgX F p j =
      stageMap DX DS g cX cS gX hgX F p i := sorry

/-- The compatible stage maps form a cocone over the identity-adjoined diagram. -/
def cocone : Cocone (diagram DX DS g hg cS F p) :=
  let compatibility : ∀ {i j : PreorderWithAdjoinedIdentities I} (arrow : i ⟶ j),
      (diagram DX DS g hg cS F p).map arrow ≫
          stageMap DX DS g cX cS gX hgX F p j =
        stageMap DX DS g cX cS gX hgX F p i :=
    (PreorderWithAdjoinedIdentities.lift_cocone_iff
      (pullbackStage DX DS g cS F p)
      (fun {_ _} hij => transition DX DS g hg cS F p hij)
      (fun {_ _ _} hij hjk => transition_comp DX DS g hg cS F p hij hjk)
      (Complex.value gX
        (AbelianSheafComplexSystem.colimitInverseImageComplex cX F) p)
      (stageMap DX DS g cX cS gX hgX F p)).mpr
      (fun {_ _} hij => stageMap_naturality DX DS g hg cX cS gX hgX F p hij)
  { pt := Complex.value gX
      (AbelianSheafComplexSystem.colimitInverseImageComplex cX F) p
    ι :=
      { app := stageMap DX DS g cX cS gX hgX F p
        naturality := fun i _ arrow =>
          (compatibility arrow).trans
            (Category.comp_id (stageMap DX DS g cX cS gX hgX F p i)).symm } }

variable [HasColimit (diagram DX DS g hg cS F p)]

/-- The canonical colimit comparison for derived higher direct images. -/
def comparison :
    colimit (diagram DX DS g hg cS F p) ⟶
      Complex.value gX
        (AbelianSheafComplexSystem.colimitInverseImageComplex cX F) p :=
  colimit.desc (diagram DX DS g hg cS F p)
    (cocone DX DS g hg cX cS gX hgX F p)

/-- The colimit comparison restricts to its named stage map on every summand. -/
theorem comparison_ι (i : I) :
    colimit.ι (diagram DX DS g hg cS F p) i ≫
        comparison DX DS g hg cX cS gX hgX F p =
      stageMap DX DS g cX cS gX hgX F p i :=
  colimit.ι_desc (cocone DX DS g hg cX cS gX hgX F p) i

/-- Uniform bounded-below affine-transition systems have isomorphic derived colimit comparison. -/
theorem isIso_comparison
    (hcX : IsLimit cX) (hcS : IsLimit cS)
    (hF : ∀ i, (F.obj i).IsStrictlyGE a) :
    IsIso (comparison DX DS g hg cX cS gX hgX F p) := sorry

end ComplexSystem

end HigherDirectImage

end AlgebraicGeometry.Scheme.Etale

end
