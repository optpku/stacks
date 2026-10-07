module

public import ReasLib.AlgebraicGeometry.RingedSite.Module.LowerShriek
public import ReasLib.AlgebraicGeometry.RingedSite.Topos.HomOfCocontinuous
public import stacks_project.Chap85.Lemma_85_16_1_Localization
public import stacks_project.Chap85.Lemma_85_16_2_Comparison
public import stacks_project.Chap85.Remark_85_15_6_Ringed_variant_Ringed

/-!
# Ringed total localization of a simplicial semi-representable object

The ringed site `((C / K)_total, O)` with `O = a⁻¹ O_C` is obtained from the unringed
total localization of Lemma 85.16.1 by inverse image of the ambient structure sheaf
along `totalForget`. Stage localizations and stage maps reuse `AtSR`.
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits Opposite
open scoped SemiRepresentableFamily Simplicial

noncomputable section

universe ι u v w

namespace RingedSite.Localization.AtSimplicialSR

open SemiRepresentableFamily
  (OverSite overTopology overSiteDiagram overSiteTotalTopology totalForget
    fiber_comp_totalForget overSite_ι_isContinuous overSite_ι_isCocontinuous overMap)

variable {X : RingedSite.{u, v, w}}
variable (K : SimplicialObject (FormalCoproduct.{ι} X.carrier))

/-- The structure sheaf `O = a⁻¹ O_C` on `(C / K)_total`, the continuous inverse image of
the ambient structure sheaf along `totalForget`. -/
abbrev ringSheaf : Sheaf (overSiteTotalTopology X.siteTopology K) RingCat.{w} :=
  Cocontinuous.inverseImageRingSheaf (totalForget K) X.structureSheaf

/-- The ringed site `((C / K)_total, O)` associated to a simplicial object of `SR(C)`. -/
def site : RingedSite.{max ι u v, max ι u v, w} :=
  ofRingSheaf (overSiteTotalTopology X.siteTopology K) (ringSheaf K)

/-- The structure sheaf of `site K` is the continuous inverse image `a⁻¹ O_C`. -/
theorem structureSheaf_spec : (site K).structureSheaf = ringSheaf K :=
  rfl

/-- Continuity of `a : (C / K)_total ⥤ C` on the packaged ringed site `site K`. -/
instance totalForget_isContinuous_site :
    (totalForget K).IsContinuous (site K).siteTopology X.siteTopology :=
  SemiRepresentableFamily.totalForget_isContinuous X.siteTopology K

/-- Cocontinuity of `a : (C / K)_total ⥤ C` on the packaged ringed site `site K`. -/
instance totalForget_isCocontinuous_site :
    (totalForget K).IsCocontinuous (site K).siteTopology X.siteTopology :=
  SemiRepresentableFamily.totalForget_isCocontinuous X.siteTopology K

/-- The morphism of ringed topoi
`a : (Sh((C / K)_total), O) ⟶ (Sh(C), O_C)`. -/
def toAmbient
    [UnivLE.{max ι u v, w}]
    [HasSheafify (overSiteTotalTopology X.siteTopology K) (Type w)]
    [∀ P : (Grothendieck (overSiteDiagram K))ᵒᵖ ⥤ Type w,
      (totalForget K).op.HasPointwiseRightKanExtension P]
    [(overSiteTotalTopology X.siteTopology K).HasSheafCompose
      (CategoryTheory.forget RingCat.{w})]
    [X.siteTopology.HasSheafCompose (CategoryTheory.forget RingCat.{w})]
    [h_forget : (totalForget K).IsCocontinuous (site K).siteTopology X.siteTopology] :
    ToposHom (site K) X :=
  @Cocontinuous.toRingedTopos (site K) X (totalForget K) h_forget inferInstance
    inferInstance inferInstance inferInstance
    (𝟙 ((totalForget K).op ⋙ X.structureSheaf.obj))

/-- The inverse-image structure map of `toAmbient` is an isomorphism, encoding
`O = a⁻¹ O_C`. -/
theorem toAmbient_structureMap_isIso
    [UnivLE.{max ι u v, w}]
    [HasSheafify (overSiteTotalTopology X.siteTopology K) (Type w)]
    [∀ P : (Grothendieck (overSiteDiagram K))ᵒᵖ ⥤ Type w,
      (totalForget K).op.HasPointwiseRightKanExtension P]
    [(overSiteTotalTopology X.siteTopology K).HasSheafCompose
      (CategoryTheory.forget RingCat.{w})]
    [X.siteTopology.HasSheafCompose (CategoryTheory.forget RingCat.{w})] :
    IsIso (toAmbient K).structureMap := sorry

/-- The morphism of ringed topoi
`a_n : (Sh(C / K_n), O_n) ⟶ (Sh(C), O_C)` of Remark 85.15.6. -/
def stageToAmbient (n : SimplexCategory)
    [UnivLE.{max ι u v, w}]
    [HasSheafify (overTopology X.siteTopology (K.obj (op n))) (Type w)]
    [∀ P : (OverSite (K.obj (op n)))ᵒᵖ ⥤ Type w,
      (SemiRepresentableFamily.forget (K.obj (op n))).op.HasPointwiseRightKanExtension P]
    [(overTopology X.siteTopology (K.obj (op n))).HasSheafCompose
      (CategoryTheory.forget RingCat.{w})]
    [X.siteTopology.HasSheafCompose (CategoryTheory.forget RingCat.{w})]
    [h_forget : (SemiRepresentableFamily.forget (K.obj (op n))).IsCocontinuous
      (AtSR.site (K.obj (op n))).siteTopology X.siteTopology] :
    ToposHom (AtSR.site (K.obj (op n))) X :=
  AtSR.toAmbient (K.obj (op n))

/-- The morphism of ringed topoi
`f_φ : (Sh(C / K_n), O_n) ⟶ (Sh(C / K_m), O_m)` induced by `φ : m ⟶ n` in
`SimplexCategory`. -/
def stageMap {m n : SimplexCategory} (φ : m ⟶ n)
    [UnivLE.{max ι u v, w}]
    [HasSheafify (overTopology X.siteTopology (K.obj (op n))) (Type w)]
    [∀ P : (OverSite (K.obj (op n)))ᵒᵖ ⥤ Type w,
      (overMap (K.map φ.op)).op.HasPointwiseRightKanExtension P]
    [(overTopology X.siteTopology (K.obj (op n))).HasSheafCompose
      (CategoryTheory.forget RingCat.{w})]
    [(overTopology X.siteTopology (K.obj (op m))).HasSheafCompose
      (CategoryTheory.forget RingCat.{w})]
    [h_map : (overMap (K.map φ.op)).IsCocontinuous
      (AtSR.site (K.obj (op n))).siteTopology (AtSR.site (K.obj (op m))).siteTopology] :
    ToposHom (AtSR.site (K.obj (op n))) (AtSR.site (K.obj (op m))) :=
  AtSR.map (K.map φ.op)

/-- Identification of the stage structure sheaf `O_n` with the inverse image of `O` along
the fiber inclusion `ι` of `(C / K)_total`. -/
def stageRingIso (n : SimplexCategory)
    [h_ι : (Grothendieck.ι (overSiteDiagram K) (op n)).IsContinuous
      (overTopology X.siteTopology (K.obj (op n))) (overSiteTotalTopology X.siteTopology K)]
    [h_stage : (SemiRepresentableFamily.forget (K.obj (op n))).IsContinuous
      (overTopology X.siteTopology (K.obj (op n))) X.siteTopology] :
    AtSR.ringSheaf (K.obj (op n)) ≅
      @Cocontinuous.inverseImageRingSheaf _ _ _ _ (overTopology X.siteTopology (K.obj (op n)))
        (overSiteTotalTopology X.siteTopology K)
        (Grothendieck.ι (overSiteDiagram K) (op n)) h_ι (ringSheaf K) where
  hom := ⟨Functor.whiskerRight (NatTrans.op (fiber_comp_totalForget K n).hom) X.structureSheaf.obj⟩
  inv := ⟨Functor.whiskerRight (NatTrans.op (fiber_comp_totalForget K n).inv) X.structureSheaf.obj⟩
  hom_inv_id := sorry
  inv_hom_id := sorry

/-- Continuity of the fiber inclusion `ι : C / K_n ⥤ (C / K)_total` on packaged ringed
sites. -/
instance stageIncl_isContinuous (n : SimplexCategory) :
    (Grothendieck.ι (overSiteDiagram K) (op n)).IsContinuous
      (AtSR.site (K.obj (op n))).siteTopology (site K).siteTopology :=
  overSite_ι_isContinuous X.siteTopology K n

/-- Cocontinuity of the fiber inclusion `ι : C / K_n ⥤ (C / K)_total` on packaged ringed
sites. -/
instance stageIncl_isCocontinuous (n : SimplexCategory) :
    (Grothendieck.ι (overSiteDiagram K) (op n)).IsCocontinuous
      (AtSR.site (K.obj (op n))).siteTopology (site K).siteTopology :=
  overSite_ι_isCocontinuous X.siteTopology K n

/-- The morphism of ringed topoi
`g_n : (Sh(C / K_n), O_n) ⟶ (Sh((C / K)_total), O)` induced by the fiber inclusion
`ι`. -/
def stageIncl (n : SimplexCategory)
    [UnivLE.{max ι u v, w}]
    [HasSheafify (overTopology X.siteTopology (K.obj (op n))) (Type w)]
    [∀ P : (OverSite (K.obj (op n)))ᵒᵖ ⥤ Type w,
      (Grothendieck.ι (overSiteDiagram K) (op n)).op.HasPointwiseRightKanExtension P]
    [(overTopology X.siteTopology (K.obj (op n))).HasSheafCompose
      (CategoryTheory.forget RingCat.{w})]
    [(overSiteTotalTopology X.siteTopology K).HasSheafCompose
      (CategoryTheory.forget RingCat.{w})]
    [h_ι_cont : (Grothendieck.ι (overSiteDiagram K) (op n)).IsContinuous
      (overTopology X.siteTopology (K.obj (op n))) (overSiteTotalTopology X.siteTopology K)]
    [h_ι : (Grothendieck.ι (overSiteDiagram K) (op n)).IsCocontinuous
      (overTopology X.siteTopology (K.obj (op n))) (overSiteTotalTopology X.siteTopology K)] :
    ToposHom (AtSR.site (K.obj (op n))) (site K) :=
  @Cocontinuous.toRingedTopos (AtSR.site (K.obj (op n))) (site K)
    (Grothendieck.ι (overSiteDiagram K) (op n)) h_ι inferInstance
    inferInstance inferInstance inferInstance (stageRingIso K n).inv.hom

/-- The inverse-image structure map of `stageIncl` is an isomorphism, encoding
`O_n = g_n⁻¹ O`. -/
theorem stageIncl_structureMap_isIso (n : SimplexCategory)
    [UnivLE.{max ι u v, w}]
    [HasSheafify (overTopology X.siteTopology (K.obj (op n))) (Type w)]
    [∀ P : (OverSite (K.obj (op n)))ᵒᵖ ⥤ Type w,
      (Grothendieck.ι (overSiteDiagram K) (op n)).op.HasPointwiseRightKanExtension P]
    [(overTopology X.siteTopology (K.obj (op n))).HasSheafCompose
      (CategoryTheory.forget RingCat.{w})]
    [(overSiteTotalTopology X.siteTopology K).HasSheafCompose
      (CategoryTheory.forget RingCat.{w})]
    [h_ι_cont : (Grothendieck.ι (overSiteDiagram K) (op n)).IsContinuous
      (overTopology X.siteTopology (K.obj (op n))) (overSiteTotalTopology X.siteTopology K)] :
    IsIso (stageIncl K n).structureMap := sorry

end RingedSite.Localization.AtSimplicialSR
