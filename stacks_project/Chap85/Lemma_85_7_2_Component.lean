/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import ReasLib.AlgebraicGeometry.RingedSite.Topos.Module
public import ReasLib.CategoryTheory.Sites.Topos.ModuleAdjunction
public import stacks_project.Chap85.Lemma_85_5_2_Total
public import stacks_project.Chap85.Lemma_85_6_1_LowerShriek
public import stacks_project.Chap85.Remark_85_7_1_Morphism

/-!
# Degree-n ringed morphisms of a morphism of ringed simplicial sites (case A)

A morphism of ringed simplicial sites `(h, hSharp)` induces component morphisms of
ringed topoi `h_n : (Sh(C_n), O_n) ⟶ (Sh(C'_n), O'_n)`, a ringed inverse-image square
with `g_n` and `g'_n`, and the mixed identity
`(g'_n)* ∘ h_total,* ≅ h_n,* ∘ g_n^*` on modules.
-/

@[expose] public section

universe u v w

open CategoryTheory CategoryTheory.Limits Opposite
open RingedSite
open scoped MorphismOfTopoiIn

noncomputable section

namespace CategoryTheory.SimplicialSites

variable {C C' : SimplexCategory ⥤ Cat.{v, u}}
variable (J : ∀ n, Precoverage (C.obj n)) (J' : ∀ n, Precoverage (C'.obj n))
variable [∀ n, HasWeakSheafify (J n).toGrothendieck (Type w)]
variable [∀ n, HasWeakSheafify (J' n).toGrothendieck (Type w)]
variable [∀ (m n : SimplexCategory) (φ : m ⟶ n) (P : (C.obj m)ᵒᵖ ⥤ Type w),
    ((C.map φ).toFunctor).op.HasLeftKanExtension P]
variable [∀ (m n : SimplexCategory) (φ : m ⟶ n) (P : (C'.obj m)ᵒᵖ ⥤ Type w),
    ((C'.map φ).toFunctor).op.HasLeftKanExtension P]
variable [IsMorphismDiagram C J] [IsMorphismDiagram C' J']
variable [HasWeakSheafify (topology C J) (Type w)]
variable [HasWeakSheafify (topology C' J') (Type w)]
variable (O : Sheaf (topology C J) RingCat.{w})
variable (O' : Sheaf (topology C' J') RingCat.{w})
variable [(topology C J).HasSheafCompose (forget RingCat.{w})]
variable [(topology C' J').HasSheafCompose (forget RingCat.{w})]
variable [∀ n, ((J n).toGrothendieck).HasSheafCompose (forget RingCat.{w})]
variable [∀ n, ((J' n).toGrothendieck).HasSheafCompose (forget RingCat.{w})]
variable [∀ n, HasSheafify ((J n).toGrothendieck) (Type w)]
variable [∀ n, HasSheafify ((J' n).toGrothendieck) (Type w)]
variable [HasSheafify (topology C J) (Type w)]
variable [HasSheafify (topology C' J') (Type w)]
variable [∀ n, ∀ P : (C.obj n)ᵒᵖ ⥤ Type w, (ofStage C n).op.HasLeftKanExtension P]
variable [∀ n, ∀ P : (C'.obj n)ᵒᵖ ⥤ Type w, (ofStage C' n).op.HasLeftKanExtension P]
variable [∀ n, ∀ P : (C.obj n)ᵒᵖ ⥤ Type w, (ofStage C n).op.HasPointwiseRightKanExtension P]
variable [∀ n, ∀ P : (C'.obj n)ᵒᵖ ⥤ Type w, (ofStage C' n).op.HasPointwiseRightKanExtension P]

/-- Lift a map of underlying type-valued sheaves to a homomorphism of sheaves of rings.
The function on sections is the given map; ring laws are deferred. -/
def homOfUnderlyingRing {D : Type u} [Category.{v} D] {K : GrothendieckTopology D}
    [K.HasSheafCompose (forget RingCat.{w})]
    {R S : Sheaf K RingCat.{w}}
    (α : (sheafCompose K (forget RingCat.{w})).obj R ⟶
      (sheafCompose K (forget RingCat.{w})).obj S) :
    R ⟶ S where
  hom :=
    { app := fun U ↦
        let source : RingCat.{w} := R.obj.obj U
        let target : RingCat.{w} := S.obj.obj U
        @RingCat.ofHom source target source.ring target.ring
        { toFun := α.hom.app U
          map_one' := sorry
          map_mul' := sorry
          map_zero' := sorry
          map_add' := sorry }
      naturality := sorry }

/-- Coefficient-forgetful comparison for continuous ring-valued pushforward along
`ofStage C n`. -/
def stageForgetIso (C : SimplexCategory ⥤ Cat.{v, u})
    (J : ∀ n, Precoverage (C.obj n))
    [∀ n, HasWeakSheafify (J n).toGrothendieck (Type w)]
    [∀ (m n : SimplexCategory) (φ : m ⟶ n) (P : (C.obj m)ᵒᵖ ⥤ Type w),
        ((C.map φ).toFunctor).op.HasLeftKanExtension P]
    [IsMorphismDiagram C J]
    [(topology C J).HasSheafCompose (forget RingCat.{w})]
    [∀ n, ((J n).toGrothendieck).HasSheafCompose (forget RingCat.{w})]
    (n : SimplexCategory) :
    (ofStage C n).sheafPushforwardContinuous RingCat.{w}
          (J n).toGrothendieck (topology C J) ⋙
        sheafCompose (J n).toGrothendieck (forget RingCat.{w}) ≅
      sheafCompose (topology C J) (forget RingCat.{w}) ⋙
        (ofStage C n).sheafPushforwardContinuous (Type w)
          (J n).toGrothendieck (topology C J) :=
  NatIso.ofComponents
    (fun P ↦
      (fullyFaithfulSheafToPresheaf (J n).toGrothendieck (Type w)).preimageIso
        (Functor.associator (ofStage C n).op P.obj (forget RingCat.{w})))
    sorry

/-- Cocontinuous pullback along `ofStage C n` is isomorphic to continuous pushforward. -/
def stageCocontinuousContinuousIso (C : SimplexCategory ⥤ Cat.{v, u})
    (J : ∀ n, Precoverage (C.obj n))
    [∀ n, HasWeakSheafify (J n).toGrothendieck (Type w)]
    [∀ (m n : SimplexCategory) (φ : m ⟶ n) (P : (C.obj m)ᵒᵖ ⥤ Type w),
        ((C.map φ).toFunctor).op.HasLeftKanExtension P]
    [IsMorphismDiagram C J]
    [∀ n, HasSheafify ((J n).toGrothendieck) (Type w)]
    [HasWeakSheafify (topology C J) (Type w)]
    [∀ n, ∀ P : (C.obj n)ᵒᵖ ⥤ Type w, (ofStage C n).op.HasPointwiseRightKanExtension P]
    (n : SimplexCategory) :
    (ofStage C n).sheafPullbackCocontinuous (Type w)
        (J n).toGrothendieck (topology C J) ≅
      (ofStage C n).sheafPushforwardContinuous (Type w)
        (J n).toGrothendieck (topology C J) :=
  NatIso.ofComponents
    (fun F ↦
      { hom :=
          Functor.CocontinuousPullback.comparisonApp (ofStage C n)
            (J n).toGrothendieck (topology C J) F
        inv :=
          ((ofStage C n).sheafPushforwardContinuous (Type w)
              (J n).toGrothendieck (topology C J)).map
            (sheafificationIso F).hom ≫
            ((ofStage C n).pushforwardContinuousSheafificationCompatibility (Type w)
                (J n).toGrothendieck (topology C J)).inv.app F.obj
        hom_inv_id := sorry
        inv_hom_id := sorry })
    sorry

/-- Underlying type-valued comparison `g_n⁻¹ O ≅ O_n`. -/
def stageRingIso_underlying (C : SimplexCategory ⥤ Cat.{v, u})
    (J : ∀ n, Precoverage (C.obj n))
    [∀ n, HasWeakSheafify (J n).toGrothendieck (Type w)]
    [∀ (m n : SimplexCategory) (φ : m ⟶ n) (P : (C.obj m)ᵒᵖ ⥤ Type w),
        ((C.map φ).toFunctor).op.HasLeftKanExtension P]
    [IsMorphismDiagram C J]
    (O : Sheaf (topology C J) RingCat.{w})
    [(topology C J).HasSheafCompose (forget RingCat.{w})]
    [∀ n, ((J n).toGrothendieck).HasSheafCompose (forget RingCat.{w})]
    [∀ n, HasSheafify ((J n).toGrothendieck) (Type w)]
    [HasWeakSheafify (topology C J) (Type w)]
    [∀ n, ∀ P : (C.obj n)ᵒᵖ ⥤ Type w, (ofStage C n).op.HasPointwiseRightKanExtension P]
    (n : SimplexCategory) :
    (sheafCompose (J n).toGrothendieck (forget RingCat.{w})).obj
        ((ofStageMorphism C J n).ringInverseImage.obj O) ≅
      (sheafCompose (J n).toGrothendieck (forget RingCat.{w})).obj
        (componentRingSheaf C J O n) :=
  ((ofStageMorphism C J n).ringInverseImageForgetIso).app O ≪≫
    (stageCocontinuousContinuousIso C J n).app
      ((sheafCompose (topology C J) (forget RingCat.{w})).obj O) ≪≫
    (stageForgetIso C J n).symm.app O

/-- The identity comparison identifies `g_n⁻¹ O` with the degree-`n` ring sheaf `O_n`. -/
def stageRingIso (C : SimplexCategory ⥤ Cat.{v, u})
    (J : ∀ n, Precoverage (C.obj n))
    [∀ n, HasWeakSheafify (J n).toGrothendieck (Type w)]
    [∀ (m n : SimplexCategory) (φ : m ⟶ n) (P : (C.obj m)ᵒᵖ ⥤ Type w),
        ((C.map φ).toFunctor).op.HasLeftKanExtension P]
    [IsMorphismDiagram C J]
    (O : Sheaf (topology C J) RingCat.{w})
    [(topology C J).HasSheafCompose (forget RingCat.{w})]
    [∀ n, ((J n).toGrothendieck).HasSheafCompose (forget RingCat.{w})]
    [∀ n, HasSheafify ((J n).toGrothendieck) (Type w)]
    [HasWeakSheafify (topology C J) (Type w)]
    [∀ n, ∀ P : (C.obj n)ᵒᵖ ⥤ Type w, (ofStage C n).op.HasPointwiseRightKanExtension P]
    (n : SimplexCategory) :
    (ofStageMorphism C J n).ringInverseImage.obj O ≅
      componentRingSheaf C J O n where
  hom := homOfUnderlyingRing (stageRingIso_underlying C J O n).hom
  inv := homOfUnderlyingRing (stageRingIso_underlying C J O n).inv
  hom_inv_id := sorry
  inv_hom_id := sorry

namespace RingedMorphism

variable {J J' O O'}
variable (f : RingedMorphism J J' O O')
variable [∀ n (P : (C'.obj n)ᵒᵖ ⥤ Type w),
    ((f.toSimplicial.app n).toFunctor).op.HasLeftKanExtension P]
variable [∀ P : (totalSite C')ᵒᵖ ⥤ Type w,
    (IsMorphism.totalFunctor f.toSimplicial).op.HasLeftKanExtension P]
variable [∀ n, (SheafOfModules.restrictScalars.{w}
    (stageMorphism C J O n).structureMap).IsRightAdjoint]
variable [∀ n, (SheafOfModules.restrictScalars.{w}
    (stageMorphism C' J' O' n).structureMap).IsRightAdjoint]

/-- Ringed inverse-image form of the degree-`n` square, before identifying `O_n` with
`g_n⁻¹ O`. -/
def inverseImage_comp_ringInverseImage (n : SimplexCategory) :
    (IsMorphism.total J J' f.toSimplicial).ringInverseImage ⋙
        (ofStageMorphism C J n).ringInverseImage ≅
      (ofStageMorphism C' J' n).ringInverseImage ⋙
        (IsMorphism.topos J J' f.toSimplicial n).ringInverseImage :=
  (MorphismOfTopoiIn.ringInverseImageCompIso
      (IsMorphism.total J J' f.toSimplicial) (ofStageMorphism C J n)).symm ≪≫
    MorphismOfTopoiIn.ringInverseImageNatIso
      ((LeftExactAdjunction.compInverseImageIso
          (IsMorphism.total J J' f.toSimplicial) (ofStageMorphism C J n)) ≪≫
        IsMorphism.inverseImage_comp J J' f.toSimplicial n ≪≫
        (LeftExactAdjunction.compInverseImageIso
            (ofStageMorphism C' J' n)
            (IsMorphism.topos J J' f.toSimplicial n)).symm) ≪≫
    MorphismOfTopoiIn.ringInverseImageCompIso
      (ofStageMorphism C' J' n)
      (IsMorphism.topos J J' f.toSimplicial n)

/-- The morphism of ringed topoi `h_n : (Sh(C_n), O_n) ⟶ (Sh(C'_n), O'_n)` with
structure map `h_n^♯ = g_n⁻¹ hSharp` after the inverse-image comparison of
Lemma 85.5.2. -/
def topos (n : SimplexCategory) :
    ToposHom (componentRingedSite C J O n) (componentRingedSite C' J' O' n) where
  toTopos := IsMorphism.topos J J' f.toSimplicial n
  structureMap :=
    (IsMorphism.topos J J' f.toSimplicial n).ringInverseImage.map
        (stageRingIso C' J' O' n).inv ≫
      (inverseImage_comp_ringInverseImage f n).inv.app O' ≫
      (ofStageMorphism C J n).ringInverseImage.map f.structureMap ≫
      (stageRingIso C J O n).hom

/-- The underlying topos morphism of `topos f n` is the unringed component `h_n`. -/
theorem topos_toTopos (n : SimplexCategory) :
    (topos f n).toTopos = IsMorphism.topos J J' f.toSimplicial n :=
  sorry

/-- The structure map of `topos f n` is `g_n⁻¹ hSharp` after identifying
`g_n⁻¹ h_total⁻¹ O' ≅ h_n⁻¹ O'_n` and `g_n⁻¹ O ≅ O_n`. -/
theorem topos_structureMap (n : SimplexCategory) :
    (topos f n).structureMap =
      (IsMorphism.topos J J' f.toSimplicial n).ringInverseImage.map
          (stageRingIso C' J' O' n).inv ≫
        (inverseImage_comp_ringInverseImage f n).inv.app O' ≫
        (ofStageMorphism C J n).ringInverseImage.map f.structureMap ≫
        (stageRingIso C J O n).hom :=
  sorry

/-- Inverse images of ringed topoi commute in the degree-`n` square:
`g_n⁻¹ ∘ h_total⁻¹ ≅ h_n⁻¹ ∘ (g'_n)⁻¹`. -/
def inverseImage_comp (n : SimplexCategory) :
    (IsMorphism.total J J' f.toSimplicial).ringInverseImage ⋙
        (ofStageMorphism C J n).ringInverseImage ≅
      (ofStageMorphism C' J' n).ringInverseImage ⋙
        (topos f n).toTopos.ringInverseImage :=
  inverseImage_comp_ringInverseImage f n

/-- Underlying type-valued sheaf of the mixed identity
`(g'_n)* ∘ h_total,* ≅ h_n,* ∘ g_n^*`. -/
def restrict_modulePushforward_underlying (n : SimplexCategory)
    (M : SheafOfModules.{w} O) :
    (Sheaf.InternalModule.ToInternal.underlying (componentRingSheaf C' J' O' n)).obj
      (((toToposHom f).modulePushforward ⋙
        (stageMorphism C' J' O' n).modulePullback).obj M) ≅
      (Sheaf.InternalModule.ToInternal.underlying (componentRingSheaf C' J' O' n)).obj
        (((stageMorphism C J O n).modulePullback ⋙
          (topos f n).modulePushforward).obj M) :=
  modulePullback_underlyingIso C' J' O' n ((toToposHom f).modulePushforward.obj M) ≪≫
    (stageRestrict C' J' (Type w) n).mapIso
      ((ToposHom.ModulePushforward.forgetIso (toToposHom f)).app M) ≪≫
    (IsMorphism.restrict_pushforward_stageRestrict J J' f.toSimplicial n).app
      ((Sheaf.InternalModule.ToInternal.underlying O).obj M) ≪≫
    (IsMorphism.topos J J' f.toSimplicial n).pushforward.mapIso
      (modulePullback_underlyingIso C J O n M).symm ≪≫
    (ToposHom.ModulePushforward.forgetIso (topos f n)).symm.app
      ((stageMorphism C J O n).modulePullback.obj M)

/-- The mixed identity `(g'_n)* ∘ h_total,* ≅ h_n,* ∘ g_n^*` as functors
`Mod(O) ⥤ Mod(O'_n)`. -/
def restrict_modulePushforward (n : SimplexCategory) :
    (toToposHom f).modulePushforward ⋙
        (stageMorphism C' J' O' n).modulePullback ≅
      (stageMorphism C J O n).modulePullback ⋙ (topos f n).modulePushforward :=
  NatIso.ofComponents
    (fun M ↦
      { hom :=
          Sheaf.InternalModule.homOfUnderlying (componentRingSheaf C' J' O' n)
            (restrict_modulePushforward_underlying f n M).hom sorry sorry
        inv :=
          Sheaf.InternalModule.homOfUnderlying (componentRingSheaf C' J' O' n)
            (restrict_modulePushforward_underlying f n M).inv sorry sorry
        hom_inv_id := sorry
        inv_hom_id := sorry })
    sorry

end RingedMorphism

end CategoryTheory.SimplicialSites
