/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.AlgebraicGeometry.Crystalline.Topology.BaseOpens
public import ReasLib.AlgebraicGeometry.Crystalline.RingedMorphism.Relative
public import ReasLib.AlgebraicGeometry.Scheme.Sites.Zariski.GlobalSections
public import ReasLib.AlgebraicGeometry.Scheme.Sites.Zariski.SmallToBig
public import ReasLib.AlgebraicGeometry.RingedSite.Topos.TwoMorphism.Arbitrary
public import ReasLib.CategoryTheory.Sites.SheafifiedRepresentable.Pullback
public import ReasLib.CategoryTheory.Sites.Topos.Cocontinuous.Sheafification
public import ReasLib.AlgebraicGeometry.Scheme.ZariskiSite.SheafEquivalence
public import Mathlib.CategoryTheory.Adjunction.Limits
public import Mathlib.CategoryTheory.Limits.Presheaf

@[expose] public section

set_option backward.privateInPublic true
set_option maxHeartbeats 2000000

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits Opposite
open AlgebraicGeometry.Scheme.Crystalline CrystallineCoefficients

noncomputable section

universe u

namespace CrystallineRingedGeometry

/-- A map to an open subscheme is supported on that open. -/
private def openMapSupport {S T : Scheme.{u}} (a : T ⟶ S) (V : S.Opens)
    (k : Over.mk a ⟶ Over.mk V.ι) : a ⁻¹ᵁ V = ⊤ :=
  (congrArg (fun b => b ⁻¹ᵁ V) k.w).symm.trans
    (congrArg (fun U => k.left ⁻¹ᵁ U) V.ι_preimage_self)

/-- A scheme map supported on an open factors through its open immersion. -/
private def supportToOpenMap {S T : Scheme.{u}} (a : T ⟶ S) (V : S.Opens)
    (q : a ⁻¹ᵁ V = ⊤) : Over.mk a ⟶ Over.mk V.ι :=
  Over.homMk (T.topIso.inv ≫ a.resLE V ⊤ q.ge)
    ((Category.assoc T.topIso.inv (a.resLE V ⊤ q.ge) V.ι).trans
      ((congrArg (fun b => T.topIso.inv ≫ b) (a.resLE_comp_ι q.ge)).trans
        ((Category.assoc T.topIso.inv (⊤ : T.Opens).ι a).symm.trans
          ((congrArg (fun b => b ≫ a) (Scheme.toIso_inv_ι T)).trans (Category.id_comp a)))))

/-- Maps over the base into an open subscheme identify with support on that open. -/
private def openSupportEquiv {S T : Scheme.{u}} (a : T ⟶ S) (V : S.Opens) :
    ULift.{u + 1} (Over.mk a ⟶ Over.mk V.ι) ≃ ULift.{u + 1} (PLift (a ⁻¹ᵁ V = ⊤)) where
  toFun k := ⟨⟨openMapSupport a V k.down⟩⟩
  invFun q := ⟨supportToOpenMap a V q.down.down⟩
  left_inv k := congrArg ULift.up (Over.OverMorphism.ext
    ((cancel_mono V.ι).mp ((supportToOpenMap a V (openMapSupport a V k.down)).w.trans k.down.w.symm)))
  right_inv _ := Subsingleton.elim _ _

variable {S X : Scheme.{u}} (I : S.IdealSheafData)
  (γ : ∀ V : S.affineOpens, DividedPowers (I.ideal V))
  (hc : ∀ (V : S.affineOpens) (a : Γ(S, V)),
    (γ V).IsDPMorphism (γ (S.affineBasicOpen a))
      (S.presheaf.map (homOfLE (S.basicOpen_le a)).op).hom)
  (x₀ : X ⟶ I.subscheme)

/-- The presheaf represented by a base open, restricted to crystalline thickenings, is its support presheaf. -/
private def thickeningOpenSupportIso (V : S.Opens) :
    (bigThickeningOverBase I γ hc x₀).op ⋙ uliftYoneda.{u + 1}.obj (Over.mk V.ι) ≅
      baseOpenPresheaf (I := I) (γ := γ) (hc := hc) (x₀ := x₀) V :=
  NatIso.ofComponents
    (fun T => (openSupportEquiv T.unop.1.thickeningToBase V).toIso)
    (fun {T T'} _ => ConcreteCategory.hom_ext _ _
      (fun _ => @Subsingleton.elim
        (ULift (PLift (T'.unop.1.thickeningToBase ⁻¹ᵁ V = ⊤))) inferInstance _ _))

variable [HasSheafify (crystallineZariskiTopology S I γ hc X x₀) (Type (u + 1))]
variable [(crystallineZariskiTopology S I γ hc X x₀).HasSheafCompose (forget RingCat.{u + 1})]
variable [∀ P : (RelativeCRIS S I γ hc X x₀)ᵒᵖ ⥤ Type (u + 1),
  (bigThickeningOverBase I γ hc x₀).op.HasPointwiseRightKanExtension P]

/-- The big crystalline structure morphism to the small Zariski base. -/
private def bigStructureToSmall :
    RingedSite.ToposHom (bigRingedSite I γ hc x₀)
      (Scheme.AssociatedModule.smallCommRingedSite .zariski S) :=
  RingedSite.ToposHom.comp (bigStructureMorphism I γ hc x₀)
    (Scheme.Crystalline.Ringed.baseSmallProjection S)

/-- Pullback of a base-open representable to the big crystalline topos is its support sheaf. -/
private def bigStructureOpenIso (V : S.Opens) :
    (bigStructureToSmall I γ hc x₀).toTopos.inverseImage.obj
      (S.smallZariskiTopology.uliftSheafifiedRepresentable.{u + 1}
        ((Scheme.smallZariskiOpenFunctor S).obj V)) ≅
      baseOpenSheaf (I := I) (γ := γ) (hc := hc) (x₀ := x₀) V :=
  let a := presheafToSheaf (crystallineZariskiTopology S I γ hc X x₀) (Type (u + 1))
  let τ := bigStructureMorphism I γ hc x₀
  τ.toTopos.inverseImage.mapIso
      (Functor.SheafifiedRepresentable.pullbackIso.{u + 1}
        (Scheme.Zariski.SmallToBig.relocalizationFunctor (𝟙 S))
        S.smallZariskiTopology (StandardTopology.zariski.overTopology S)
        ((Scheme.smallZariskiOpenFunctor S).obj V)).symm ≪≫
    τ.toTopos.inverseImage.mapIso
      ((StandardTopology.zariski.overTopology S).uliftSheafifiedRepresentableFunctor.{u + 1}.mapIso
        ((Over.mapId S).app (Over.mk V.ι))) ≪≫
    ((Functor.CocontinuousPullback.sheafificationCompatibility.{u + 1, u + 1, u, u, u + 1}
      (bigThickeningOverBase I γ hc x₀) (crystallineZariskiTopology S I γ hc X x₀)
      (StandardTopology.zariski.overTopology S)).app
        (uliftYoneda.{u + 1}.obj (Over.mk V.ι))).symm ≪≫
    a.mapIso (thickeningOpenSupportIso I γ hc x₀ V) ≪≫
    (sheafificationIso (baseOpenSheaf V)).symm

variable {p : ℕ} [Fact p.Prime]
variable (s : S ⟶ Spec (.of (ULift.{u} (Int.LocalizationAtPrime p))))
variable (hpX : ∀ U : X.affineOpens, IsNilpotent (p : Γ(X, U)))
variable [HasSheafify (smallCrystallineTopology p S I γ hc s X x₀ hpX) (Type (u + 1))]
variable [(smallCrystallineTopology p S I γ hc s X x₀ hpX).HasSheafCompose (forget RingCat.{u + 1})]
variable [∀ P : (smallCrystallineSite S I γ hc X x₀)ᵒᵖ ⥤ Type (u + 1),
  (smallCrystallineInclusion S I γ hc X x₀).op.HasPointwiseRightKanExtension P]

/-- Pullback of a base-open representable to the small crystalline topos is restricted support. -/
private def smallStructureOpenIso (V : S.Opens) :
    (structureMorphismToSmall I γ hc x₀ s hpX).toTopos.inverseImage.obj
      (S.smallZariskiTopology.uliftSheafifiedRepresentable.{u + 1}
        ((Scheme.smallZariskiOpenFunctor S).obj V)) ≅
      (smallToBigRinged I γ hc x₀ s hpX).toTopos.inverseImage.obj
        (baseOpenSheaf (I := I) (γ := γ) (hc := hc) (x₀ := x₀) V) :=
  (smallToBigRinged I γ hc x₀ s hpX).toTopos.inverseImage.mapIso
    (bigStructureOpenIso I γ hc x₀ V)

variable {S' X' : Scheme.{u}} (I' : S'.IdealSheafData)
  (γ' : ∀ V : S'.affineOpens, DividedPowers (I'.ideal V))
  (hc' : ∀ (V : S'.affineOpens) (a : Γ(S', V)),
    (γ' V).IsDPMorphism (γ' (S'.affineBasicOpen a))
      (S'.presheaf.map (homOfLE (S'.basicOpen_le a)).op).hom)
  (s' : S' ⟶ Spec (.of (ULift.{u} (Int.LocalizationAtPrime p))))
  (x'₀ : X' ⟶ I'.subscheme) (f : X ⟶ X')
  (g : DividedPowerSchemeHom I I' s s') (hf : f ≫ x'₀ = x₀ ≫ g.zeroFiberMap)
  (hpX' : ∀ U : X'.affineOpens, IsNilpotent (p : Γ(X', U)))
  (hγ : ∀ (V : S'.affineOpens) (W : S.affineOpens) (hVW : W.1 ≤ g.base ⁻¹ᵁ V.1),
    (γ' V).IsDPMorphism (γ W) (g.base.appLE V W hVW).hom)
variable [HasSheafify (crystallineZariskiTopology S' I' γ' hc' X' x'₀) (Type (u + 1))]
variable [HasSheafify (smallCrystallineTopology p S' I' γ' hc' s' X' x'₀ hpX') (Type (u + 1))]
variable [(crystallineZariskiTopology S' I' γ' hc' X' x'₀).HasSheafCompose (forget RingCat.{u + 1})]
variable [(smallCrystallineTopology p S' I' γ' hc' s' X' x'₀ hpX').HasSheafCompose (forget RingCat.{u + 1})]
variable [∀ P : (RelativeCRIS S I γ hc X x₀)ᵒᵖ ⥤ Type (u + 1),
  (CrystallineFunctor.of f g hf hpX hpX' hγ).toRelativeFunctor.op.HasPointwiseRightKanExtension P]
variable [∀ P : (RelativeCRIS S' I' γ' hc' X' x'₀)ᵒᵖ ⥤ Type (u + 1),
  (bigThickeningOverBase I' γ' hc' x'₀).op.HasPointwiseRightKanExtension P]
variable [∀ P : (smallCrystallineSite S' I' γ' hc' X' x'₀)ᵒᵖ ⥤ Type (u + 1),
  (smallCrystallineInclusion S' I' γ' hc' X' x'₀).op.HasPointwiseRightKanExtension P]
variable [∀ P : (smallCrystallineSite S' I' γ' hc' X' x'₀)ᵒᵖ ⥤ Type (u + 1),
  (smallCrystallineInclusion S' I' γ' hc' X' x'₀).op.HasLeftKanExtension P]

/-- Pullback of base-open support along the big crystalline morphism is support on the inverse image open. -/
private def bigMorphismSupportIso (V : S'.Opens) :
    (bigRingedMorphism I γ hc x₀ I' γ' hc' s s' x'₀ f g hf hpX hpX' hγ).toTopos.inverseImage.obj
      (baseOpenSheaf (I := I') (γ := γ') (hc := hc') (x₀ := x'₀) V) ≅
        baseOpenSheaf (I := I) (γ := γ) (hc := hc) (x₀ := x₀) (g.base ⁻¹ᵁ V) :=
  (sheafificationIso
    (baseOpenSheaf (I := I) (γ := γ) (hc := hc) (x₀ := x₀) (g.base ⁻¹ᵁ V))).symm

/-- The crystalline morphism followed by the target structure morphism. -/
private abbrev structureRouteLeft :=
  RingedSite.ToposHom.comp
    (smallRingedMorphism I γ hc x₀ I' γ' hc' s s' x'₀ f g hf hpX hpX' hγ)
    (structureMorphismToSmall I' γ' hc' x'₀ s' hpX')

/-- The source structure morphism followed by the base's small-Zariski morphism. -/
private abbrev structureRouteRight :=
  RingedSite.ToposHom.comp (structureMorphismToSmall I γ hc x₀ s hpX)
    (Scheme.Crystalline.Ringed.zariskiHom g.base).toToposHom

/-- The structure square comparison on representable base opens, using supported extension and actual geometric pullback. -/
private def structureOpenIso (V : S'.Opens) :
    (structureRouteLeft I γ hc x₀ s hpX I' γ' hc' s' x'₀ f g hf hpX' hγ).toTopos.inverseImage.obj
      (S'.smallZariskiTopology.uliftSheafifiedRepresentable.{u + 1}
        ((Scheme.smallZariskiOpenFunctor S').obj V)) ≅
    (structureRouteRight I γ hc x₀ s hpX I' s' g).toTopos.inverseImage.obj
      (S'.smallZariskiTopology.uliftSheafifiedRepresentable.{u + 1}
        ((Scheme.smallZariskiOpenFunctor S').obj V)) :=
  let i := smallToBigRinged I γ hc x₀ s hpX
  let i' := smallCrystallineInclusion S' I' γ' hc' X' x'₀
  let f₀ := smallRingedMorphism I γ hc x₀ I' γ' hc' s s' x'₀ f g hf hpX hpX' hγ
  let b := bigRingedMorphism I γ hc x₀ I' γ' hc' s s' x'₀ f g hf hpX hpX' hγ
  let π' := bigToSmallRinged I' γ' hc' x'₀ s' hpX'
  let τ := structureMorphismToSmall I γ hc x₀ s hpX
  let first := f₀.toTopos.inverseImage.mapIso (smallStructureOpenIso I' γ' hc' x'₀ s' hpX' V)
  let middle := i.toTopos.inverseImage.mapIso
    (b.toTopos.inverseImage.mapIso
      (π'.toTopos.inverseImage.mapIso
        ((Functor.CocontinuousPullback.comparisonIso.{u + 1, u, u, u + 1, u + 1} i'
          (smallCrystallineTopology p S' I' γ' hc' s' X' x'₀ hpX')
          (crystallineZariskiTopology S' I' γ' hc' X' x'₀)).app (baseOpenSheaf V)) ≪≫
        baseOpenExtensionIso p s' hpX' V) ≪≫
      bigMorphismSupportIso I γ hc x₀ s hpX I' γ' hc' s' x'₀ f g hf hpX' hγ V)
  let last := τ.toTopos.inverseImage.mapIso
    ((Functor.SheafifiedRepresentable.pullbackIso.{u + 1} (Scheme.smallZariskiPullback g.base)
      S'.smallZariskiTopology S.smallZariskiTopology
        ((Scheme.smallZariskiOpenFunctor S').obj V)).symm ≪≫
      S.smallZariskiTopology.uliftSheafifiedRepresentableFunctor.{u + 1}.mapIso
        ((Scheme.smallZariskiPullbackOpenFunctorIso g.base).app V)) ≪≫
    smallStructureOpenIso I γ hc x₀ s hpX (g.base ⁻¹ᵁ V)
  first ≪≫ middle ≪≫ last.symm

/-- The comparison on an arbitrary small-Zariski representable, transported from its open range. -/
private def structureRepresentableIso (U : S'.smallZariskiSite) :
    (structureRouteLeft I γ hc x₀ s hpX I' γ' hc' s' x'₀ f g hf hpX' hγ).toTopos.inverseImage.obj
      (S'.smallZariskiTopology.uliftSheafifiedRepresentable.{u + 1} U) ≅
    (structureRouteRight I γ hc x₀ s hpX I' s' g).toTopos.inverseImage.obj
      (S'.smallZariskiTopology.uliftSheafifiedRepresentable.{u + 1} U) :=
  let e := S'.smallZariskiTopology.uliftSheafifiedRepresentableFunctor.{u + 1}.mapIso
    (Scheme.smallZariskiOpenCounitIsoApp S' U)
  (structureRouteLeft I γ hc x₀ s hpX I' γ' hc' s' x'₀ f g hf hpX' hγ).toTopos.inverseImage.mapIso e.symm ≪≫
    structureOpenIso I γ hc x₀ s hpX I' γ' hc' s' x'₀ f g hf hpX' hγ ((Scheme.smallZariskiRangeFunctor S').obj U) ≪≫
    (structureRouteRight I γ hc x₀ s hpX I' s' g).toTopos.inverseImage.mapIso e

/-- Naturality of the comparison on representable small-Zariski sheaves. -/
private def structureRepresentableLaws : Prop :=
  ∀ (U V : S'.smallZariskiSite) (k : U ⟶ V),
    (structureRouteLeft I γ hc x₀ s hpX I' γ' hc' s' x'₀ f g hf hpX' hγ).toTopos.inverseImage.map
        (S'.smallZariskiTopology.uliftSheafifiedRepresentableFunctor.{u + 1}.map k) ≫
      (structureRepresentableIso I γ hc x₀ s hpX I' γ' hc' s' x'₀ f g hf hpX' hγ V).hom =
    (structureRepresentableIso I γ hc x₀ s hpX I' γ' hc' s' x'₀ f g hf hpX' hγ U).hom ≫
      (structureRouteRight I γ hc x₀ s hpX I' s' g).toTopos.inverseImage.map
        (S'.smallZariskiTopology.uliftSheafifiedRepresentableFunctor.{u + 1}.map k)

/-- The representable comparison as a natural isomorphism. -/
private def structureRepresentableComparison (h : structureRepresentableLaws I γ hc x₀ s hpX I' γ' hc' s' x'₀ f g hf hpX' hγ) :
    S'.smallZariskiTopology.uliftSheafifiedRepresentableFunctor.{u + 1} ⋙
      (structureRouteLeft I γ hc x₀ s hpX I' γ' hc' s' x'₀ f g hf hpX' hγ).toTopos.inverseImage ≅
    S'.smallZariskiTopology.uliftSheafifiedRepresentableFunctor.{u + 1} ⋙
      (structureRouteRight I γ hc x₀ s hpX I' s' g).toTopos.inverseImage :=
  NatIso.ofComponents (structureRepresentableIso I γ hc x₀ s hpX I' γ' hc' s' x'₀ f g hf hpX' hγ) (fun k => h _ _ k)

/-- Extension of a transformation on representables by the canonical colimit of elements. -/
private def representableColimitMap
    {C : Type (u + 1)} [Category.{u} C] {D : Type (u + 2)} [Category.{u + 1} D]
    (F G : (Cᵒᵖ ⥤ Type (u + 1)) ⥤ D)
    {H : D ⥤ (Cᵒᵖ ⥤ Type (u + 1))} (adj : F ⊣ H)
    (e : uliftYoneda.{u + 1} ⋙ F ⟶ uliftYoneda.{u + 1} ⋙ G)
    (P : Cᵒᵖ ⥤ Type (u + 1)) : F.obj P ⟶ G.obj P :=
  let hF : PreservesColimit (Presheaf.functorToRepresentables.{u + 1} P) F :=
    adj.leftAdjoint_preservesColimits.preservesColimitsOfShape.preservesColimit
  (@isColimitOfPreserves _ _ _ _ _ _ _ F _
    (Presheaf.colimitOfRepresentable.{u + 1} P) hF).desc
    { pt := G.obj P
      ι := Functor.whiskerLeft (CategoryOfElements.π P).leftOp e ≫
        (G.mapCocone (Presheaf.coconeOfRepresentable.{u + 1} P)).ι }

/-- The two colimit extensions satisfy inverse identities and naturality. -/
private def structureColimitLaws (h : structureRepresentableLaws I γ hc x₀ s hpX I' γ' hc' s' x'₀ f g hf hpX' hγ) : Prop :=
  let a := presheafToSheaf S'.smallZariskiTopology (Type (u + 1))
  let F := a ⋙ (structureRouteLeft I γ hc x₀ s hpX I' γ' hc' s' x'₀ f g hf hpX' hγ).toTopos.inverseImage
  let G := a ⋙ (structureRouteRight I γ hc x₀ s hpX I' s' g).toTopos.inverseImage
  let e := structureRepresentableComparison I γ hc x₀ s hpX I' γ' hc' s' x'₀ f g hf hpX' hγ h
  let forward := representableColimitMap F G ((sheafificationAdjunction S'.smallZariskiTopology (Type (u + 1))).comp (structureRouteLeft I γ hc x₀ s hpX I' γ' hc' s' x'₀ f g hf hpX' hγ).toTopos.adjunction) e.hom
  let backward := representableColimitMap G F ((sheafificationAdjunction S'.smallZariskiTopology (Type (u + 1))).comp (structureRouteRight I γ hc x₀ s hpX I' s' g).toTopos.adjunction) e.inv
  (∀ P, forward P ≫ backward P = 𝟙 (F.obj P)) ∧
  (∀ P, backward P ≫ forward P = 𝟙 (G.obj P)) ∧
  (∀ (P Q : S'.smallZariskiSiteᵒᵖ ⥤ Type (u + 1)) (k : P ⟶ Q),
    F.map k ≫ forward Q = forward P ≫ G.map k)

/-- The comparison on all presheaves obtained by extending both representable directions. -/
private def structurePresheafComparison (h : structureRepresentableLaws I γ hc x₀ s hpX I' γ' hc' s' x'₀ f g hf hpX' hγ)
    (h' : structureColimitLaws I γ hc x₀ s hpX I' γ' hc' s' x'₀ f g hf hpX' hγ h) :
    presheafToSheaf S'.smallZariskiTopology (Type (u + 1)) ⋙
      (structureRouteLeft I γ hc x₀ s hpX I' γ' hc' s' x'₀ f g hf hpX' hγ).toTopos.inverseImage ≅
    presheafToSheaf S'.smallZariskiTopology (Type (u + 1)) ⋙
      (structureRouteRight I γ hc x₀ s hpX I' s' g).toTopos.inverseImage :=
  let a := presheafToSheaf S'.smallZariskiTopology (Type (u + 1))
  let F := a ⋙ (structureRouteLeft I γ hc x₀ s hpX I' γ' hc' s' x'₀ f g hf hpX' hγ).toTopos.inverseImage
  let G := a ⋙ (structureRouteRight I γ hc x₀ s hpX I' s' g).toTopos.inverseImage
  let e := structureRepresentableComparison I γ hc x₀ s hpX I' γ' hc' s' x'₀ f g hf hpX' hγ h
  NatIso.ofComponents
    (fun P => { hom := representableColimitMap F G ((sheafificationAdjunction S'.smallZariskiTopology (Type (u + 1))).comp (structureRouteLeft I γ hc x₀ s hpX I' γ' hc' s' x'₀ f g hf hpX' hγ).toTopos.adjunction) e.hom P
                inv := representableColimitMap G F ((sheafificationAdjunction S'.smallZariskiTopology (Type (u + 1))).comp (structureRouteRight I γ hc x₀ s hpX I' s' g).toTopos.adjunction) e.inv P
                hom_inv_id := h'.1 P
                inv_hom_id := h'.2.1 P })
    (fun k => h'.2.2 _ _ k)

/-- The comparison of inverse images on small-Zariski sheaves. -/
private def structureInverseImageComparison (h : structureRepresentableLaws I γ hc x₀ s hpX I' γ' hc' s' x'₀ f g hf hpX' hγ)
    (h' : structureColimitLaws I γ hc x₀ s hpX I' γ' hc' s' x'₀ f g hf hpX' hγ h) :
    (structureRouteLeft I γ hc x₀ s hpX I' γ' hc' s' x'₀ f g hf hpX' hγ).toTopos.inverseImage ≅ (structureRouteRight I γ hc x₀ s hpX I' s' g).toTopos.inverseImage :=
  let L := (structureRouteLeft I γ hc x₀ s hpX I' γ' hc' s' x'₀ f g hf hpX' hγ).toTopos.inverseImage
  let R := (structureRouteRight I γ hc x₀ s hpX I' s' g).toTopos.inverseImage
  let a := sheafificationNatIso S'.smallZariskiTopology (Type (u + 1))
  Functor.isoWhiskerRight a L ≪≫
    Functor.isoWhiskerLeft (sheafToPresheaf S'.smallZariskiTopology (Type (u + 1)))
      (structurePresheafComparison I γ hc x₀ s hpX I' γ' hc' s' x'₀ f g hf hpX' hγ h h') ≪≫
    (Functor.isoWhiskerRight a R).symm

/-- The comparison of direct images induced by uniqueness of right adjoints. -/
private def structureDirectImageComparison (h : structureRepresentableLaws I γ hc x₀ s hpX I' γ' hc' s' x'₀ f g hf hpX' hγ)
    (h' : structureColimitLaws I γ hc x₀ s hpX I' γ' hc' s' x'₀ f g hf hpX' hγ h) :
    (structureRouteLeft I γ hc x₀ s hpX I' γ' hc' s' x'₀ f g hf hpX' hγ).toTopos.pushforward ≅ (structureRouteRight I γ hc x₀ s hpX I' s' g).toTopos.pushforward :=
  ((structureRouteLeft I γ hc x₀ s hpX I' γ' hc' s' x'₀ f g hf hpX' hγ).toTopos.adjunction.ofNatIsoLeft
    (structureInverseImageComparison I γ hc x₀ s hpX I' γ' hc' s' x'₀ f g hf hpX' hγ h h')).rightAdjointUniq
      (structureRouteRight I γ hc x₀ s hpX I' s' g).toTopos.adjunction

/-- The base-open comparison is natural, its colimit extensions are inverse, and the induced direct-image map respects the structure ring. -/
theorem structureComparison_laws :
    structureRepresentableLaws I γ hc x₀ s hpX I' γ' hc' s' x'₀ f g hf hpX' hγ ∧
    ∀ h : structureRepresentableLaws I γ hc x₀ s hpX I' γ' hc' s' x'₀ f g hf hpX' hγ,
      structureColimitLaws I γ hc x₀ s hpX I' γ' hc' s' x'₀ f g hf hpX' hγ h ∧
      ∀ h' : structureColimitLaws I γ hc x₀ s hpX I' γ' hc' s' x'₀ f g hf hpX' hγ h,
        (structureRouteLeft I γ hc x₀ s hpX I' γ' hc' s' x'₀ f g hf hpX' hγ).directStructureMap ≫
          (@MorphismOfTopoiIn.ringDirectImageNatTrans
            (Scheme.AssociatedModule.smallCommRingedSite .zariski S').carrier
            (Scheme.AssociatedModule.smallCommRingedSite .zariski S').carrier.str
            (liftedRingedSite I γ hc x₀ p s hpX).carrier
            (liftedRingedSite I γ hc x₀ p s hpX).carrier.str
            (Scheme.AssociatedModule.smallCommRingedSite .zariski S').siteTopology
            (liftedRingedSite I γ hc x₀ p s hpX).siteTopology
            (structureRouteLeft I γ hc x₀ s hpX I' γ' hc' s' x'₀ f g hf hpX' hγ).toTopos
            (structureRouteRight I γ hc x₀ s hpX I' s' g).toTopos inferInstance inferInstance
            (structureDirectImageComparison I γ hc x₀ s hpX I' γ' hc' s' x'₀ f g hf hpX' hγ h h').hom).app
              (liftedRingedSite I γ hc x₀ p s hpX).structureSheaf =
        (structureRouteRight I γ hc x₀ s hpX I' s' g).directStructureMap := sorry

/-- The crystalline structure morphisms commute with the actual small-Zariski base morphism as ringed topoi. -/
def structureComparison : RingedSite.ToposHom.TwoIso (structureRouteLeft I γ hc x₀ s hpX I' γ' hc' s' x'₀ f g hf hpX' hγ) (structureRouteRight I γ hc x₀ s hpX I' s' g) where
  homIso := structureDirectImageComparison I γ hc x₀ s hpX I' γ' hc' s' x'₀ f g hf hpX' hγ
    (structureComparison_laws I γ hc x₀ s hpX I' γ' hc' s' x'₀ f g hf hpX' hγ).1
    ((structureComparison_laws I γ hc x₀ s hpX I' γ' hc' s' x'₀ f g hf hpX' hγ).2 (structureComparison_laws I γ hc x₀ s hpX I' γ' hc' s' x'₀ f g hf hpX' hγ).1).1
  comm := ((structureComparison_laws I γ hc x₀ s hpX I' γ' hc' s' x'₀ f g hf hpX' hγ).2 (structureComparison_laws I γ hc x₀ s hpX I' γ' hc' s' x'₀ f g hf hpX' hγ).1).2
    ((structureComparison_laws I γ hc x₀ s hpX I' γ' hc' s' x'₀ f g hf hpX' hγ).2 (structureComparison_laws I γ hc x₀ s hpX I' γ' hc' s' x'₀ f g hf hpX' hγ).1).1

/-- The small-Zariski global-function actions agree with the crystalline base actions and with pullback along the base scheme map. -/
theorem structureBaseActions_laws :
    ((structureMorphismToSmall I γ hc x₀ s hpX).globalSectionsMap.hom.comp
      (Scheme.Zariski.Small.globalFunctionsIso S).symm.toRingHom =
        CrystallineCoefficients.baseToGlobalSections I γ hc x₀ p s hpX) ∧
    ((structureMorphismToSmall I' γ' hc' x'₀ s' hpX').globalSectionsMap.hom.comp
      (Scheme.Zariski.Small.globalFunctionsIso S').symm.toRingHom =
        CrystallineCoefficients.baseToGlobalSections I' γ' hc' x'₀ p s' hpX') ∧
    ((Scheme.Crystalline.Ringed.zariskiHom g.base).toToposHom.globalSectionsMap.hom.comp
      (Scheme.Zariski.Small.globalFunctionsIso S').symm.toRingHom =
        (Scheme.Zariski.Small.globalFunctionsIso S).symm.toRingHom.comp
          (CrystallineCoefficients.baseRingMap g.base)) := sorry

end CrystallineRingedGeometry
