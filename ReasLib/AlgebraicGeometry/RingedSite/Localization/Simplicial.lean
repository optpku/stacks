module

public import ReasLib.AlgebraicGeometry.RingedSite.Localization.Family
public import ReasLib.AlgebraicGeometry.RingedSite.Topos.HomOfCocontinuous
public import ReasLib.CategoryTheory.Sites.Family.Simplicial.Comparison

/-!
# Ringed total localization of a simplicial family

The ambient sheaf of rings restricts to the total localization and its fibers.
The augmentation and fiber inclusions carry their canonical coefficient maps.
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
theorem totalForget_isContinuous_site :
    (totalForget K).IsContinuous (site K).siteTopology X.siteTopology :=
  SemiRepresentableFamily.totalForget_isContinuous X.siteTopology K

/-- Cocontinuity of `a : (C / K)_total ⥤ C` on the packaged ringed site `site K`. -/
theorem totalForget_isCocontinuous_site :
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
    [X.siteTopology.HasSheafCompose (CategoryTheory.forget RingCat.{w})] :
    ToposHom (site K) X :=
  @Cocontinuous.toRingedTopos (site K) X (totalForget K)
    (totalForget_isCocontinuous_site K) inferInstance
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
`a_n : (Sh(C / K_n), O_n) ⟶ (Sh(C), O_C)`. -/
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

-- Local declaration justification (metaprogramming implementation): Export this
-- private proof law for the Prop-valued fields of an exposed construction.
set_option backward.privateInPublic true in
/-- The coefficient comparison followed by its inverse is the identity. -/
private theorem stageRingHom_inv_id (n : SimplexCategory)
    [h_ι : (Grothendieck.ι (overSiteDiagram K) (op n)).IsContinuous
      (overTopology X.siteTopology (K.obj (op n))) (overSiteTotalTopology X.siteTopology K)]
    [h_stage : (SemiRepresentableFamily.forget (K.obj (op n))).IsContinuous
      (overTopology X.siteTopology (K.obj (op n))) X.siteTopology] :
    let h : AtSR.ringSheaf (K.obj (op n)) ⟶
      @Cocontinuous.inverseImageRingSheaf _ _ _ _ (overTopology X.siteTopology (K.obj (op n)))
        (overSiteTotalTopology X.siteTopology K)
        (Grothendieck.ι (overSiteDiagram K) (op n)) h_ι (ringSheaf K) :=
      ⟨Functor.whiskerRight (NatTrans.op (fiber_comp_totalForget K n).hom) X.structureSheaf.obj⟩
    let i : (@Cocontinuous.inverseImageRingSheaf _ _ _ _ (overTopology X.siteTopology (K.obj (op n)))
        (overSiteTotalTopology X.siteTopology K)
        (Grothendieck.ι (overSiteDiagram K) (op n)) h_ι (ringSheaf K)) ⟶
      AtSR.ringSheaf (K.obj (op n)) :=
      ⟨Functor.whiskerRight (NatTrans.op (fiber_comp_totalForget K n).inv) X.structureSheaf.obj⟩
    h ≫ i = 𝟙 _ := sorry

-- Local declaration justification (metaprogramming implementation): Export this
-- private proof law for the Prop-valued fields of an exposed construction.
set_option backward.privateInPublic true in
/-- The inverse coefficient comparison followed by the comparison is the identity. -/
private theorem stageRingInv_hom_id (n : SimplexCategory)
    [h_ι : (Grothendieck.ι (overSiteDiagram K) (op n)).IsContinuous
      (overTopology X.siteTopology (K.obj (op n))) (overSiteTotalTopology X.siteTopology K)]
    [h_stage : (SemiRepresentableFamily.forget (K.obj (op n))).IsContinuous
      (overTopology X.siteTopology (K.obj (op n))) X.siteTopology] :
    let h : AtSR.ringSheaf (K.obj (op n)) ⟶
      @Cocontinuous.inverseImageRingSheaf _ _ _ _ (overTopology X.siteTopology (K.obj (op n)))
        (overSiteTotalTopology X.siteTopology K)
        (Grothendieck.ι (overSiteDiagram K) (op n)) h_ι (ringSheaf K) :=
      ⟨Functor.whiskerRight (NatTrans.op (fiber_comp_totalForget K n).hom) X.structureSheaf.obj⟩
    let i : (@Cocontinuous.inverseImageRingSheaf _ _ _ _ (overTopology X.siteTopology (K.obj (op n)))
        (overSiteTotalTopology X.siteTopology K)
        (Grothendieck.ι (overSiteDiagram K) (op n)) h_ι (ringSheaf K)) ⟶
      AtSR.ringSheaf (K.obj (op n)) :=
      ⟨Functor.whiskerRight (NatTrans.op (fiber_comp_totalForget K n).inv) X.structureSheaf.obj⟩
    i ≫ h = 𝟙 _ := sorry

-- Local declaration justification (metaprogramming implementation): The exposed
-- isomorphism uses private inverse-law proofs only in its Prop-valued fields.
set_option backward.privateInPublic true in
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
  hom_inv_id := stageRingHom_inv_id K n
  inv_hom_id := stageRingInv_hom_id K n

/-- Continuity of the fiber inclusion `ι : C / K_n ⥤ (C / K)_total` on packaged ringed
sites. -/
theorem stageIncl_isContinuous (n : SimplexCategory) :
    (Grothendieck.ι (overSiteDiagram K) (op n)).IsContinuous
      (AtSR.site (K.obj (op n))).siteTopology (site K).siteTopology :=
  overSite_ι_isContinuous X.siteTopology K n

/-- Cocontinuity of the fiber inclusion `ι : C / K_n ⥤ (C / K)_total` on packaged ringed
sites. -/
theorem stageIncl_isCocontinuous (n : SimplexCategory) :
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
