module

public import ReasLib.AlgebraicGeometry.Scheme.Module.Etale.CurveComparison.CompactificationChange

@[expose] public section
open CategoryTheory CategoryTheory.Limits Opposite
open AlgebraicGeometry AlgebraicGeometry.Scheme
noncomputable section
universe u v w

namespace ActualExtensionBaseChange
variable {U U' C D : Scheme.{u}}
variable (j : U ⟶ C) (j' : U' ⟶ D) (g : U' ⟶ U) (f : D ⟶ C)
variable [IsOpenImmersion j] [IsOpenImmersion j']
variable (hcart : IsPullback g j' j f)

include hcart in
/-- The two explicit pullback projections satisfy the square equation. -/
theorem site_condition (V : U.Etale) :
    pullback.fst V.hom g ≫ (V.hom ≫ j) =
      (pullback.snd V.hom g ≫ j') ≫ f := sorry

/-- The cartesian site comparison uses the two actual pullback projections. -/
def siteMap (V : U.Etale) :
    (smallEtalePullback g ⋙ etaleRestriction j').obj V ⟶
      (etaleRestriction j ⋙ smallEtalePullback f).obj V :=
  MorphismProperty.Over.homMk
    (pullback.lift (pullback.fst V.hom g) (pullback.snd V.hom g ≫ j')
      (site_condition j j' g f hcart V))
    (pullback.lift_snd _ _ _)

instance siteMap_isIso (V : U.Etale) : IsIso (siteMap j j' g f hcart V) := sorry

def siteIso : smallEtalePullback g ⋙ etaleRestriction j' ≅
    etaleRestriction j ⋙ smallEtalePullback f :=
  NatIso.ofComponents (fun V ↦ asIso (siteMap j j' g f hcart V)) (fun _ ↦ sorry)

variable (A : Type v) [Category.{w} A]

/-- The right-adjoint comparison restricts the same sections along the
displayed site isomorphism; it works for both module and additive sheaves. -/
def restrictionIso :
    (smallEtalePullback f).sheafPushforwardContinuous A C.smallEtaleTopology D.smallEtaleTopology ⋙
      etaleRestrictionSheaf j A ≅
    etaleRestrictionSheaf j' A ⋙
      (smallEtalePullback g).sheafPushforwardContinuous A U.smallEtaleTopology U'.smallEtaleTopology :=
  NatIso.ofComponents (fun F ↦
    { hom := ObjectProperty.homMk
        { app := fun V ↦ F.obj.map ((siteIso j j' g f hcart).hom.app V.unop).op
          naturality := sorry }
      inv := ObjectProperty.homMk
        { app := fun V ↦ F.obj.map ((siteIso j j' g f hcart).inv.app V.unop).op
          naturality := sorry }
      hom_inv_id := sorry
      inv_hom_id := sorry }) (fun _ ↦ sorry)

variable [HasWeakSheafify C.smallEtaleTopology A]
variable [HasWeakSheafify D.smallEtaleTopology A]
variable [HasWeakSheafify U'.smallEtaleTopology A]
variable [∀ F : U.Etaleᵒᵖ ⥤ A, (etaleRestriction j).op.HasLeftKanExtension F]
variable [∀ F : U'.Etaleᵒᵖ ⥤ A, (etaleRestriction j').op.HasLeftKanExtension F]
variable [∀ F : C.Etaleᵒᵖ ⥤ A, (smallEtalePullback f).op.HasLeftKanExtension F]
variable [∀ F : U.Etaleᵒᵖ ⥤ A, (smallEtalePullback g).op.HasLeftKanExtension F]

/-- The canonical base-change isomorphism for extension by zero is the
adjoint mate of the explicit pullback-square comparison. This supplies the
field-base-change and semilinear coefficient map, without choosing an iso. -/
def extensionIso :
    etaleExtensionByZero j A ⋙
      (smallEtalePullback f).sheafPullback A C.smallEtaleTopology D.smallEtaleTopology ≅
    (smallEtalePullback g).sheafPullback A U.smallEtaleTopology U'.smallEtaleTopology ⋙
      etaleExtensionByZero j' A :=
  (((etaleExtensionByZero_adjunction j A).comp
    ((smallEtalePullback f).sheafAdjunctionContinuous A C.smallEtaleTopology D.smallEtaleTopology)).ofNatIsoRight
      (restrictionIso j j' g f hcart A)).leftAdjointUniq
    (((smallEtalePullback g).sheafAdjunctionContinuous A U.smallEtaleTopology U'.smallEtaleTopology).comp
      (etaleExtensionByZero_adjunction j' A))

end ActualExtensionBaseChange
