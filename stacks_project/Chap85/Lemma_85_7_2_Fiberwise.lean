/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import ReasLib.AlgebraicGeometry.RingedSite.Topos.Module
public import ReasLib.CategoryTheory.Sites.Topos.ModuleAdjunction
public import stacks_project.Chap85.Lemma_85_5_2_Fiberwise
public import stacks_project.Chap85.Lemma_85_6_1_Fiber
public import stacks_project.Chap85.Remark_85_7_1_Fiberwise

/-!
# Degree-n ringed morphisms of a fiberwise morphism of ringed simplicial sites (case B)

A morphism of ringed simplicial sites `(h, hSharp)` in the Grothendieck presentation
induces component morphisms of ringed topoi `h_n`, a ringed inverse-image square with
`g_n` and `g'_n`, and the mixed identity
`(g'_n)* ∘ h_total,* ≅ h_n,* ∘ g_n^*` on modules.
-/

@[expose] public section

universe u v w

open CategoryTheory CategoryTheory.Limits Opposite Functor
open RingedSite
open scoped MorphismOfTopoiIn

noncomputable section

namespace CategoryTheory.Grothendieck

variable {F F' : SimplicialObject Cat.{v, u}}
variable (J : ∀ n, Precoverage (F.obj n)) (J' : ∀ n, Precoverage (F'.obj n))
variable [IsFiberwiseSite F J] [IsFiberwiseSite F' J']
variable [∀ n, HasSheafify (J n).toGrothendieck (Type w)]
variable [∀ n, HasSheafify (J' n).toGrothendieck (Type w)]
variable [HasSheafify (topology F J) (Type w)]
variable [HasSheafify (topology F' J') (Type w)]
variable [HasWeakSheafify (topology F J) (Type w)]
variable [HasWeakSheafify (topology F' J') (Type w)]
variable [∀ n, HasWeakSheafify (J n).toGrothendieck (Type w)]
variable [∀ n, HasWeakSheafify (J' n).toGrothendieck (Type w)]
variable (O : Sheaf (topology F J) RingCat.{w})
variable (O' : Sheaf (topology F' J') RingCat.{w})
variable [(topology F J).HasSheafCompose (CategoryTheory.forget RingCat.{w})]
variable [(topology F' J').HasSheafCompose (CategoryTheory.forget RingCat.{w})]
variable [∀ n, ((J n).toGrothendieck).HasSheafCompose (CategoryTheory.forget RingCat.{w})]
variable [∀ n, ((J' n).toGrothendieck).HasSheafCompose (CategoryTheory.forget RingCat.{w})]
variable [∀ n, ∀ P : (F.obj (op n))ᵒᵖ ⥤ Type w,
    (ι F (op n)).op.HasLeftKanExtension P]
variable [∀ n, ∀ P : (F'.obj (op n))ᵒᵖ ⥤ Type w,
    (ι F' (op n)).op.HasLeftKanExtension P]
variable [∀ n, ∀ P : (F.obj (op n))ᵒᵖ ⥤ Type w,
    (ι F (op n)).op.HasPointwiseRightKanExtension P]
variable [∀ n, ∀ P : (F'.obj (op n))ᵒᵖ ⥤ Type w,
    (ι F' (op n)).op.HasPointwiseRightKanExtension P]
variable [∀ (m n : SimplexCategory) (φ : m ⟶ n) (P : (F.obj (op n))ᵒᵖ ⥤ Type w),
    ((F.map φ.op).toFunctor).op.HasPointwiseRightKanExtension P]
variable [∀ (m n : SimplexCategory) (φ : m ⟶ n) (P : (F'.obj (op n))ᵒᵖ ⥤ Type w),
    ((F'.map φ.op).toFunctor).op.HasPointwiseRightKanExtension P]

/-- Lift a map of underlying type-valued sheaves to a homomorphism of sheaves of rings.
The function on sections is the given map; ring laws are deferred. -/
def homOfUnderlyingRing {D : Type u} [Category.{v} D] {K : GrothendieckTopology D}
    [K.HasSheafCompose (CategoryTheory.forget RingCat.{w})]
    {R S : Sheaf K RingCat.{w}}
    (α : (sheafCompose K (CategoryTheory.forget RingCat.{w})).obj R ⟶
      (sheafCompose K (CategoryTheory.forget RingCat.{w})).obj S) :
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
`ι F (op n)`. -/
def fiberStageForgetIso (F : SimplicialObject Cat.{v, u})
    (J : ∀ n, Precoverage (F.obj n))
    [IsFiberwiseSite F J]
    [(topology F J).HasSheafCompose (CategoryTheory.forget RingCat.{w})]
    [∀ n, ((J n).toGrothendieck).HasSheafCompose (CategoryTheory.forget RingCat.{w})]
    (n : SimplexCategory) :
    (ι F (op n)).sheafPushforwardContinuous RingCat.{w}
          (J (op n)).toGrothendieck (topology F J) ⋙
        sheafCompose (J (op n)).toGrothendieck (CategoryTheory.forget RingCat.{w}) ≅
      sheafCompose (topology F J) (CategoryTheory.forget RingCat.{w}) ⋙
        (ι F (op n)).sheafPushforwardContinuous (Type w)
          (J (op n)).toGrothendieck (topology F J) :=
  NatIso.ofComponents
    (fun P ↦
      (fullyFaithfulSheafToPresheaf (J (op n)).toGrothendieck (Type w)).preimageIso
        (Functor.associator (ι F (op n)).op P.obj (CategoryTheory.forget RingCat.{w})))
    sorry

/-- Cocontinuous pullback along `ι F (op n)` is isomorphic to continuous pushforward. -/
def fiberStageCocontinuousContinuousIso (F : SimplicialObject Cat.{v, u})
    (J : ∀ n, Precoverage (F.obj n))
    [IsFiberwiseSite F J]
    [∀ n, HasSheafify (J n).toGrothendieck (Type w)]
    [HasWeakSheafify (topology F J) (Type w)]
    [∀ n, ∀ P : (F.obj (op n))ᵒᵖ ⥤ Type w,
        (ι F (op n)).op.HasPointwiseRightKanExtension P]
    (n : SimplexCategory) :
    (ι F (op n)).sheafPullbackCocontinuous (Type w)
        (J (op n)).toGrothendieck (topology F J) ≅
      (ι F (op n)).sheafPushforwardContinuous (Type w)
        (J (op n)).toGrothendieck (topology F J) :=
  NatIso.ofComponents
    (fun G ↦
      { hom :=
          Functor.CocontinuousPullback.comparisonApp (ι F (op n))
            (J (op n)).toGrothendieck (topology F J) G
        inv :=
          ((ι F (op n)).sheafPushforwardContinuous (Type w)
              (J (op n)).toGrothendieck (topology F J)).map
            (sheafificationIso G).hom ≫
            ((ι F (op n)).pushforwardContinuousSheafificationCompatibility (Type w)
                (J (op n)).toGrothendieck (topology F J)).inv.app G.obj
        hom_inv_id := sorry
        inv_hom_id := sorry })
    sorry

/-- Underlying type-valued comparison `g_n⁻¹ O ≅ O_n` in case B. -/
def fiberStageRingIso_underlying (F : SimplicialObject Cat.{v, u})
    (J : ∀ n, Precoverage (F.obj n))
    [IsFiberwiseSite F J]
    (O : Sheaf (topology F J) RingCat.{w})
    [(topology F J).HasSheafCompose (CategoryTheory.forget RingCat.{w})]
    [∀ n, ((J n).toGrothendieck).HasSheafCompose (CategoryTheory.forget RingCat.{w})]
    [∀ n, HasSheafify (J n).toGrothendieck (Type w)]
    [HasSheafify (topology F J) (Type w)]
    [HasWeakSheafify (topology F J) (Type w)]
    [∀ n, ∀ P : (F.obj (op n))ᵒᵖ ⥤ Type w,
        (ι F (op n)).op.HasPointwiseRightKanExtension P]
    (n : SimplexCategory) :
    (sheafCompose (J (op n)).toGrothendieck (CategoryTheory.forget RingCat.{w})).obj
        ((fiberMorphism F J n).ringInverseImage.obj O) ≅
      (sheafCompose (J (op n)).toGrothendieck (CategoryTheory.forget RingCat.{w})).obj
        (fiberComponentRingSheaf F J O n) :=
  ((fiberMorphism F J n).ringInverseImageForgetIso).app O ≪≫
    (fiberStageCocontinuousContinuousIso F J n).app
      ((sheafCompose (topology F J) (CategoryTheory.forget RingCat.{w})).obj O) ≪≫
    (fiberStageForgetIso F J n).symm.app O

/-- The identity comparison identifies `g_n⁻¹ O` with the degree-`n` ring sheaf `O_n`
in case B. -/
def fiberStageRingIso (F : SimplicialObject Cat.{v, u})
    (J : ∀ n, Precoverage (F.obj n))
    [IsFiberwiseSite F J]
    (O : Sheaf (topology F J) RingCat.{w})
    [(topology F J).HasSheafCompose (CategoryTheory.forget RingCat.{w})]
    [∀ n, ((J n).toGrothendieck).HasSheafCompose (CategoryTheory.forget RingCat.{w})]
    [∀ n, HasSheafify (J n).toGrothendieck (Type w)]
    [HasSheafify (topology F J) (Type w)]
    [HasWeakSheafify (topology F J) (Type w)]
    [∀ n, ∀ P : (F.obj (op n))ᵒᵖ ⥤ Type w,
        (ι F (op n)).op.HasPointwiseRightKanExtension P]
    (n : SimplexCategory) :
    (fiberMorphism F J n).ringInverseImage.obj O ≅
      fiberComponentRingSheaf F J O n where
  hom := homOfUnderlyingRing (fiberStageRingIso_underlying F J O n).hom
  inv := homOfUnderlyingRing (fiberStageRingIso_underlying F J O n).inv
  hom_inv_id := sorry
  inv_hom_id := sorry

namespace RingedMorphism

variable {J J' O O'}
variable (f : RingedMorphism J J' O O')
variable [∀ n (P : (F.obj n)ᵒᵖ ⥤ Type w),
    ((f.toSimplicial.app n).toFunctor).op.HasPointwiseRightKanExtension P]
variable [∀ P : (Grothendieck F)ᵒᵖ ⥤ Type w,
    (IsFiberwiseMorphism.totalFunctor f.toSimplicial).op.HasPointwiseRightKanExtension P]
variable [∀ n, ∀ P : (F.obj (op n))ᵒᵖ ⥤ Type w,
    ((f.toSimplicial.app (op n)).toFunctor ⋙ ι F' (op n)).op.HasPointwiseRightKanExtension P]
variable [∀ n, ∀ P : (F.obj (op n))ᵒᵖ ⥤ Type w,
    (ι F (op n) ⋙ IsFiberwiseMorphism.totalFunctor f.toSimplicial).op.HasPointwiseRightKanExtension P]
variable [∀ n, (SheafOfModules.restrictScalars.{w}
    (fiberStageMorphism F J O n).structureMap).IsRightAdjoint]
variable [∀ n, (SheafOfModules.restrictScalars.{w}
    (fiberStageMorphism F' J' O' n).structureMap).IsRightAdjoint]

/-- Ringed inverse-image form of the degree-`n` square, before identifying `O_n` with
`g_n⁻¹ O`. -/
def inverseImage_comp_ringInverseImage (n : SimplexCategory) :
    (IsFiberwiseMorphism.total J J' f.toSimplicial).ringInverseImage ⋙
        (fiberMorphism F J n).ringInverseImage ≅
      (fiberMorphism F' J' n).ringInverseImage ⋙
        (IsFiberwiseMorphism.topos J J' f.toSimplicial n).ringInverseImage :=
  (MorphismOfTopoiIn.ringInverseImageCompIso
      (IsFiberwiseMorphism.total J J' f.toSimplicial) (fiberMorphism F J n)).symm ≪≫
    MorphismOfTopoiIn.ringInverseImageNatIso
      ((LeftExactAdjunction.compInverseImageIso
          (IsFiberwiseMorphism.total J J' f.toSimplicial) (fiberMorphism F J n)) ≪≫
        IsFiberwiseMorphism.inverseImage_comp J J' f.toSimplicial n ≪≫
        (LeftExactAdjunction.compInverseImageIso
            (fiberMorphism F' J' n)
            (IsFiberwiseMorphism.topos J J' f.toSimplicial n)).symm) ≪≫
    MorphismOfTopoiIn.ringInverseImageCompIso
      (fiberMorphism F' J' n)
      (IsFiberwiseMorphism.topos J J' f.toSimplicial n)

/-- The morphism of ringed topoi `h_n : (Sh(C_n), O_n) ⟶ (Sh(C'_n), O'_n)` in case B,
with structure map `h_n^♯ = g_n⁻¹ hSharp` after the inverse-image comparison of
Lemma 85.5.2. -/
def topos (n : SimplexCategory) :
    ToposHom (fiberComponentRingedSite F J O n) (fiberComponentRingedSite F' J' O' n) where
  toTopos := IsFiberwiseMorphism.topos J J' f.toSimplicial n
  structureMap :=
    (IsFiberwiseMorphism.topos J J' f.toSimplicial n).ringInverseImage.map
        (fiberStageRingIso F' J' O' n).inv ≫
      (inverseImage_comp_ringInverseImage f n).inv.app O' ≫
      (fiberMorphism F J n).ringInverseImage.map f.structureMap ≫
      (fiberStageRingIso F J O n).hom

/-- The underlying topos morphism of `topos f n` is the unringed component `h_n`. -/
theorem topos_toTopos (n : SimplexCategory) :
    (topos f n).toTopos = IsFiberwiseMorphism.topos J J' f.toSimplicial n :=
  sorry

/-- The structure map of `topos f n` is `g_n⁻¹ hSharp` after identifying
`g_n⁻¹ h_total⁻¹ O' ≅ h_n⁻¹ O'_n` and `g_n⁻¹ O ≅ O_n`. -/
theorem topos_structureMap (n : SimplexCategory) :
    (topos f n).structureMap =
      (IsFiberwiseMorphism.topos J J' f.toSimplicial n).ringInverseImage.map
          (fiberStageRingIso F' J' O' n).inv ≫
        (inverseImage_comp_ringInverseImage f n).inv.app O' ≫
        (fiberMorphism F J n).ringInverseImage.map f.structureMap ≫
        (fiberStageRingIso F J O n).hom :=
  sorry

/-- Inverse images of ringed topoi commute in the degree-`n` square in case B:
`g_n⁻¹ ∘ h_total⁻¹ ≅ h_n⁻¹ ∘ (g'_n)⁻¹`. -/
def inverseImage_comp (n : SimplexCategory) :
    (IsFiberwiseMorphism.total J J' f.toSimplicial).ringInverseImage ⋙
        (fiberMorphism F J n).ringInverseImage ≅
      (fiberMorphism F' J' n).ringInverseImage ⋙
        (topos f n).toTopos.ringInverseImage :=
  inverseImage_comp_ringInverseImage f n

/-- Mixed identity of Lemma 85.5.2 transported from `g_n⁻¹` to restriction `F ↦ F_n`. -/
def restrict_pushforward_fiberRestrict (n : SimplexCategory) :
    (IsFiberwiseMorphism.total J J' f.toSimplicial).pushforward ⋙
        fiberRestrict F' J' (Type w) n ≅
      fiberRestrict F J (Type w) n ⋙
        (IsFiberwiseMorphism.topos J J' f.toSimplicial n).pushforward :=
  Functor.isoWhiskerLeft
      ((IsFiberwiseMorphism.total J J' f.toSimplicial).pushforward)
      (fiberInverseImageIso F' J' n).symm ≪≫
    IsFiberwiseMorphism.restrict_pushforward J J' f.toSimplicial n ≪≫
    Functor.isoWhiskerRight (fiberInverseImageIso F J n)
      (IsFiberwiseMorphism.topos J J' f.toSimplicial n).pushforward

/-- Underlying type-valued sheaf of the mixed identity
`(g'_n)* ∘ h_total,* ≅ h_n,* ∘ g_n^*` in case B. -/
def restrict_modulePushforward_underlying (n : SimplexCategory)
    (M : SheafOfModules.{w} O) :
    (Sheaf.InternalModule.ToInternal.underlying (fiberComponentRingSheaf F' J' O' n)).obj
      (((toToposHom f).modulePushforward ⋙
        (fiberStageMorphism F' J' O' n).modulePullback).obj M) ≅
      (Sheaf.InternalModule.ToInternal.underlying (fiberComponentRingSheaf F' J' O' n)).obj
        (((fiberStageMorphism F J O n).modulePullback ⋙
          (topos f n).modulePushforward).obj M) :=
  fiberModulePullback_underlyingIso F' J' O' n
      ((toToposHom f).modulePushforward.obj M) ≪≫
    (fiberRestrict F' J' (Type w) n).mapIso
      ((ToposHom.ModulePushforward.forgetIso (toToposHom f)).app M) ≪≫
    (restrict_pushforward_fiberRestrict f n).app
      ((Sheaf.InternalModule.ToInternal.underlying O).obj M) ≪≫
    (IsFiberwiseMorphism.topos J J' f.toSimplicial n).pushforward.mapIso
      (fiberModulePullback_underlyingIso F J O n M).symm ≪≫
    (ToposHom.ModulePushforward.forgetIso (topos f n)).symm.app
      ((fiberStageMorphism F J O n).modulePullback.obj M)

/-- The mixed identity `(g'_n)* ∘ h_total,* ≅ h_n,* ∘ g_n^*` as functors
`Mod(O) ⥤ Mod(O'_n)` in case B. -/
def restrict_modulePushforward (n : SimplexCategory) :
    (toToposHom f).modulePushforward ⋙
        (fiberStageMorphism F' J' O' n).modulePullback ≅
      (fiberStageMorphism F J O n).modulePullback ⋙ (topos f n).modulePushforward :=
  NatIso.ofComponents
    (fun M ↦
      { hom :=
          Sheaf.InternalModule.homOfUnderlying (fiberComponentRingSheaf F' J' O' n)
            (restrict_modulePushforward_underlying f n M).hom sorry sorry
        inv :=
          Sheaf.InternalModule.homOfUnderlying (fiberComponentRingSheaf F' J' O' n)
            (restrict_modulePushforward_underlying f n M).inv sorry sorry
        hom_inv_id := sorry
        inv_hom_id := sorry })
    sorry

end RingedMorphism

end CategoryTheory.Grothendieck
