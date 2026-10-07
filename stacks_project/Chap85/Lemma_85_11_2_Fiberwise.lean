module

public import Mathlib.Algebra.Category.ModuleCat.Sheaf.Abelian
public import Mathlib.Algebra.Homology.QuasiIso
public import Mathlib.AlgebraicTopology.AlternatingFaceMapComplex
public import Mathlib.CategoryTheory.Adjunction.CompositionIso
public import stacks_project.Chap85.Lemma_85_6_1_Fiber

/-!
# Alternating-face complex of `g_{n!}(a_n^* G)` on a fiberwise simplicial site

In Situation 85.3.3 case B, with a morphism of ringed topoi
`a : (Sh(C_total), O) ⟶ (Sh(D), O_D)`, the simplicial sheaf of `O`-modules
`n ↦ g_{n!}(a_n^* G)` on the total Grothendieck construction, its augmentation
to `a^* G`, and the associated alternating-face chain complex. Here `g_{n!}` is
as in Lemma 85.6.1.
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits Opposite Functor AlgebraicTopology
open HomologicalComplex RingedSite
open scoped Simplicial

noncomputable section

universe u v w uD vD

namespace CategoryTheory.Grothendieck

variable (F : SimplicialObject Cat.{v, u}) (J : ∀ n, Precoverage (F.obj n))
variable [IsFiberwiseSite F J]
variable (O : Sheaf (topology F J) RingCat.{w})
variable [(topology F J).HasSheafCompose (CategoryTheory.forget RingCat.{w})]
variable [∀ n, ((J n).toGrothendieck).HasSheafCompose (CategoryTheory.forget RingCat.{w})]
variable [(topology F J).HasSheafCompose (CategoryTheory.forget₂ RingCat.{w} AddCommGrpCat.{w})]
variable [∀ n, ((J n).toGrothendieck).HasSheafCompose (CategoryTheory.forget₂ RingCat.{w} AddCommGrpCat.{w})]
variable [∀ n, HasSheafify (J n).toGrothendieck (Type w)]
variable [HasSheafify (topology F J) (Type w)]
variable [∀ n, ∀ P : (F.obj (op n))ᵒᵖ ⥤ Type w,
    (ι F (op n)).op.HasPointwiseRightKanExtension P]
variable [∀ (m n : SimplexCategory) (φ : m ⟶ n) (P : (F.obj (op n))ᵒᵖ ⥤ Type w),
    ((F.map φ.op).toFunctor).op.HasPointwiseRightKanExtension P]
variable [∀ n, (SheafOfModules.restrictScalars.{w}
    (fiberStageMorphism F J O n).structureMap).IsRightAdjoint]
variable [∀ {m n : SimplexCategory} (φ : m ⟶ n),
    (SheafOfModules.restrictScalars.{w}
      (fiberRingedToposMap F J O φ).structureMap).IsRightAdjoint]
variable [∀ n, HasWeakSheafify (J n).toGrothendieck AddCommGrpCat.{w}]
variable [HasWeakSheafify (topology F J) AddCommGrpCat.{w}]
variable [∀ n, HasSheafify (J n).toGrothendieck AddCommGrpCat.{w}]
variable [HasSheafify (topology F J) AddCommGrpCat.{w}]
variable [∀ n, ((J n).toGrothendieck).WEqualsLocallyBijective AddCommGrpCat.{w}]
variable [(topology F J).WEqualsLocallyBijective AddCommGrpCat.{w}]
variable {D : RingedSite.{uD, vD, w}}
variable [D.siteTopology.HasSheafCompose (CategoryTheory.forget RingCat.{w})]
variable (a : ToposHom (fiberTotalRingedSite F J O) D)
variable [(SheafOfModules.restrictScalars.{w} a.structureMap).IsRightAdjoint]
variable [∀ n, (SheafOfModules.restrictScalars.{w}
    ((fiberStageMorphism F J O n).comp a).structureMap).IsRightAdjoint]
variable (G : SheafOfModules.{w} D.structureSheaf)

/-- Reconstruct a module morphism from an underlying type-valued sheaf map. -/
def moduleHomOfUnderlying.{uY, vY} {Y : RingedSite.{uY, vY, w}}
    [Y.siteTopology.HasSheafCompose (CategoryTheory.forget RingCat.{w})]
    {M N : SheafOfModules.{w} Y.structureSheaf}
    (α : (Sheaf.InternalModule.ToInternal.underlying Y.structureSheaf).obj M ⟶
      (Sheaf.InternalModule.ToInternal.underlying Y.structureSheaf).obj N) :
    M ⟶ N :=
  Sheaf.InternalModule.homOfUnderlying Y.structureSheaf α sorry sorry

/-- Lift an underlying-sheaf isomorphism of module functors to a module-functor isomorphism. -/
def moduleIsoOfUnderlying.{uX, vX, uY, vY}
    {X : RingedSite.{uX, vX, w}} {Y : RingedSite.{uY, vY, w}}
    [X.siteTopology.HasSheafCompose (CategoryTheory.forget RingCat.{w})]
    [Y.siteTopology.HasSheafCompose (CategoryTheory.forget RingCat.{w})]
    {F G : SheafOfModules.{w} X.structureSheaf ⥤ SheafOfModules.{w} Y.structureSheaf}
    (e : F ⋙ Sheaf.InternalModule.ToInternal.underlying Y.structureSheaf ≅
      G ⋙ Sheaf.InternalModule.ToInternal.underlying Y.structureSheaf) :
    F ≅ G :=
  NatIso.ofComponents
    (fun M ↦
      { hom := moduleHomOfUnderlying (e.hom.app M)
        inv := moduleHomOfUnderlying (e.inv.app M)
        hom_inv_id := sorry
        inv_hom_id := sorry })
    sorry

/-- Underlying type-valued sheaves identify the composite of module pushforwards along `g_n`
and `a` with module pushforward along `g_n` then `a`. -/
def fiberStageModulePushforwardCompUnderlyingIso (n : SimplexCategory) :
    ((fiberStageMorphism F J O n).modulePushforward ⋙ a.modulePushforward) ⋙
      Sheaf.InternalModule.ToInternal.underlying D.structureSheaf ≅
      ((fiberStageMorphism F J O n).comp a).modulePushforward ⋙
        Sheaf.InternalModule.ToInternal.underlying D.structureSheaf :=
  Functor.associator _ _ _ ≪≫
    Functor.isoWhiskerLeft (fiberStageMorphism F J O n).modulePushforward
      (ToposHom.ModulePushforward.forgetIso a) ≪≫
    (Functor.associator _ _ _).symm ≪≫
    Functor.isoWhiskerRight (ToposHom.ModulePushforward.forgetIso (fiberStageMorphism F J O n))
      a.toTopos.pushforward ≪≫
    Functor.associator _ _ _ ≪≫
    (ToposHom.ModulePushforward.forgetIso ((fiberStageMorphism F J O n).comp a)).symm

/-- Module pushforwards along `g_n` and `a` compose as `(g_n then a)_*` in case B. -/
def fiberStageModulePushforwardCompIso (n : SimplexCategory) :
    (fiberStageMorphism F J O n).modulePushforward ⋙ a.modulePushforward ≅
      ((fiberStageMorphism F J O n).comp a).modulePushforward :=
  moduleIsoOfUnderlying (fiberStageModulePushforwardCompUnderlyingIso F J O a n)

/-- Identification of the degree-`n` restriction `g_n^*(a^* G)` with `a_n^* G` in case B. -/
def fiberRestrictModulePullbackIso (n : SimplexCategory) :
    (fiberStageMorphism F J O n).modulePullback.obj (a.modulePullback.obj G) ≅
      ((fiberStageMorphism F J O n).comp a).modulePullback.obj G :=
  (Adjunction.leftAdjointCompIso a.moduleAdjunction
      (fiberStageMorphism F J O n).moduleAdjunction
      ((fiberStageMorphism F J O n).comp a).moduleAdjunction
      (fiberStageModulePushforwardCompIso F J O a n)).app G

/-- `fiberRestrictModulePullbackIso` is the component of the left-adjoint composition
comparison. -/
theorem fiberRestrictModulePullbackIso_eq (n : SimplexCategory) :
    fiberRestrictModulePullbackIso F J O a G n =
      (Adjunction.leftAdjointCompIso a.moduleAdjunction
          (fiberStageMorphism F J O n).moduleAdjunction
          ((fiberStageMorphism F J O n).comp a).moduleAdjunction
          (fiberStageModulePushforwardCompIso F J O a n)).app G :=
  sorry

/-- Continuous restriction of `a^* G` along the degree-`n` fiber inclusion. -/
def fiberAugmentation_stage_underlyingIso (n : SimplexCategory) :
    (Sheaf.InternalModule.ToInternal.underlying (fiberComponentRingSheaf F J O n)).obj
      (((fiberStageMorphism F J O n).comp a).modulePullback.obj G) ≅
      ((ι F (op n)).sheafPushforwardContinuous (Type w)
        (J (op n)).toGrothendieck (topology F J)).obj
        ((Sheaf.InternalModule.ToInternal.underlying O).obj (a.modulePullback.obj G)) :=
  (Sheaf.InternalModule.ToInternal.underlying (fiberComponentRingSheaf F J O n)).mapIso
      (fiberRestrictModulePullbackIso F J O a G n).symm ≪≫
    fiberModulePullback_underlyingIso F J O n (a.modulePullback.obj G)

/-- The `ιNatTrans` 2-cell on underlying type-valued sheaves of `a_n^* G` and `a_m^* G`. -/
def fiberModulePullbackStageComp_underlying {n m : SimplexCategory} (φ : n ⟶ m) :
    ((F.map φ.op).toFunctor.sheafPullbackCocontinuous (Type w)
        (J (op m)).toGrothendieck (J (op n)).toGrothendieck).obj
      ((Sheaf.InternalModule.ToInternal.underlying
          (fiberComponentRingSheaf F J O n)).obj
        (((fiberStageMorphism F J O n).comp a).modulePullback.obj G)) ⟶
      ((ι F (op m)).sheafPushforwardContinuous (Type w)
        (J (op m)).toGrothendieck (topology F J)).obj
        ((Sheaf.InternalModule.ToInternal.underlying O).obj
          (a.modulePullback.obj G)) :=
  (presheafToSheaf ((J (op m)).toGrothendieck) (Type w)).map
      (whiskerLeft (F.map φ.op).toFunctor.op
        ((sheafToPresheaf ((J (op n)).toGrothendieck) (Type w)).map
          (fiberAugmentation_stage_underlyingIso F J O a G n).hom)) ≫
    (presheafToSheaf ((J (op m)).toGrothendieck) (Type w)).map
      (whiskerRight (NatTrans.op (ιNatTrans φ.op))
        ((Sheaf.InternalModule.ToInternal.underlying O).obj
          (a.modulePullback.obj G)).obj) ≫
    (sheafificationAdjunction ((J (op m)).toGrothendieck) (Type w)).counit.app
      (((ι F (op m)).sheafPushforwardContinuous (Type w)
          (J (op m)).toGrothendieck (topology F J)).obj
        ((Sheaf.InternalModule.ToInternal.underlying O).obj
          (a.modulePullback.obj G)))

/-- Geometric inverse-image comparison `f_φ^{-1}(a_n^* G) ⟶ restrict(a_m^* G)` along
`ιNatTrans`. -/
def fiberModulePullbackStageComp_geometric {n m : SimplexCategory} (φ : n ⟶ m) :
    ((fiberRingedToposMap F J O φ).toTopos.moduleInverseImage
        (fiberComponentRingSheaf F J O n)).obj
      (((fiberStageMorphism F J O n).comp a).modulePullback.obj G) ⟶
      (SheafOfModules.restrictScalars (fiberRingedToposMap F J O φ).structureMap).obj
        (((fiberStageMorphism F J O m).comp a).modulePullback.obj G) :=
  Sheaf.InternalModule.homOfUnderlying
    ((fiberRingedToposMap F J O φ).toTopos.ringInverseImage.obj
      (fiberComponentRingSheaf F J O n))
    (((fiberRingedToposMap F J O φ).toTopos.moduleInverseImageForgetIso
        (fiberComponentRingSheaf F J O n)).hom.app
        (((fiberStageMorphism F J O n).comp a).modulePullback.obj G) ≫
      fiberModulePullbackStageComp_underlying F J O a G φ ≫
      (fiberAugmentation_stage_underlyingIso F J O a G m).inv ≫
      (fiberRingedToposMap_restrictScalars_forgetIso F J O φ
          (((fiberStageMorphism F J O m).comp a).modulePullback.obj G)).inv)
    sorry sorry

/-- Restriction `f_φ^*(a_n^* G) ⟶ a_m^* G` along the simplicial 2-cell in case B. -/
def fiberModulePullbackStageComp {n m : SimplexCategory} (φ : n ⟶ m) :
    (fiberRingedToposMap F J O φ).modulePullback.obj
      (((fiberStageMorphism F J O n).comp a).modulePullback.obj G) ⟶
      ((fiberStageMorphism F J O m).comp a).modulePullback.obj G :=
  (ToposHom.ModulePullback.scalarHomEquiv (fiberRingedToposMap F J O φ)
      (((fiberRingedToposMap F J O φ).toTopos.moduleInverseImage
          (fiberComponentRingSheaf F J O n)).obj
        (((fiberStageMorphism F J O n).comp a).modulePullback.obj G))
      (((fiberStageMorphism F J O m).comp a).modulePullback.obj G)).symm
    (fiberModulePullbackStageComp_geometric F J O a G φ)

/-- The comparison `f_φ^*(a_n^* G) ⟶ a_m^* G` is an isomorphism, as
`a_m ∘ f_φ = a_n` on ringed topoi. -/
instance fiberModulePullbackStageComp_isIso {n m : SimplexCategory} (φ : n ⟶ m) :
    IsIso (fiberModulePullbackStageComp F J O a G φ) :=
  sorry

/-- Inverse-image form of `a_m ∘ f_φ = a_n` on modules in case B. -/
def fiberModulePullbackStageCompIso {n m : SimplexCategory} (φ : n ⟶ m) :
    ((fiberStageMorphism F J O m).comp a).modulePullback.obj G ≅
      (fiberRingedToposMap F J O φ).modulePullback.obj
        (((fiberStageMorphism F J O n).comp a).modulePullback.obj G) :=
  (asIso (fiberModulePullbackStageComp F J O a G φ)).symm

/-- The structure map `g_{m!}(a_m^* G) ⟶ g_{n!}(a_n^* G)` induced by a fiberwise simplex
operator `φ : n ⟶ m`. -/
def fiberLowerShriekModulePullback_map {n m : SimplexCategory} (φ : n ⟶ m) :
    (fiberModuleLowerShriek F J O m).obj
      (((fiberStageMorphism F J O m).comp a).modulePullback.obj G) ⟶
    (fiberModuleLowerShriek F J O n).obj
      (((fiberStageMorphism F J O n).comp a).modulePullback.obj G) :=
  ((fiberModuleLowerShriek.adjunction F J O m).homEquiv
      (((fiberStageMorphism F J O m).comp a).modulePullback.obj G)
      ((fiberModuleLowerShriek F J O n).obj
        (((fiberStageMorphism F J O n).comp a).modulePullback.obj G))).symm
    ((fiberModulePullbackStageCompIso F J O a G φ).hom ≫
      fiberModuleLowerShriek_component F J O φ
        (((fiberStageMorphism F J O n).comp a).modulePullback.obj G) ≫
      (fiberModuleInverseImageIsoModulePullback F J O m).inv.app
        ((fiberModuleLowerShriek F J O n).obj
          (((fiberStageMorphism F J O n).comp a).modulePullback.obj G)))

/-- Identity simplex operators induce identity structure maps in case B. -/
theorem fiberLowerShriekModulePullback_map_id (n : SimplexCategory) :
    fiberLowerShriekModulePullback_map F J O a G (𝟙 n) =
      𝟙 ((fiberModuleLowerShriek F J O n).obj
        (((fiberStageMorphism F J O n).comp a).modulePullback.obj G)) :=
  sorry

/-- Structure maps of `n ↦ g_{n!}(a_n^* G)` are functorial in fiberwise simplex operators. -/
theorem fiberLowerShriekModulePullback_map_comp {l n m : SimplexCategory}
    (ψ : l ⟶ n) (φ : n ⟶ m) :
    fiberLowerShriekModulePullback_map F J O a G (ψ ≫ φ) =
      fiberLowerShriekModulePullback_map F J O a G φ ≫
        fiberLowerShriekModulePullback_map F J O a G ψ :=
  sorry

/-- Opposite identity operators act as identity maps in case B. -/
theorem fiberLowerShriekModulePullback_map_id_op (n : SimplexCategoryᵒᵖ) :
    fiberLowerShriekModulePullback_map F J O a G (𝟙 n.unop) =
      𝟙 ((fiberModuleLowerShriek F J O n.unop).obj
        (((fiberStageMorphism F J O n.unop).comp a).modulePullback.obj G)) :=
  sorry

/-- Opposite composition of simplex operators acts as composition of structure maps in case B. -/
theorem fiberLowerShriekModulePullback_map_comp_op {n m p : SimplexCategoryᵒᵖ}
    (f : n ⟶ m) (g : m ⟶ p) :
    fiberLowerShriekModulePullback_map F J O a G (f ≫ g).unop =
      fiberLowerShriekModulePullback_map F J O a G f.unop ≫
        fiberLowerShriekModulePullback_map F J O a G g.unop :=
  sorry

/-- The simplicial sheaf of `O`-modules `n ↦ g_{n!}(a_n^* G)` on the total fiberwise site. -/
def fiberLowerShriekModulePullback : SimplicialObject (SheafOfModules.{w} O) where
  obj n :=
    (fiberModuleLowerShriek F J O n.unop).obj
      (((fiberStageMorphism F J O n.unop).comp a).modulePullback.obj G)
  map f := fiberLowerShriekModulePullback_map F J O a G f.unop
  map_id := fiberLowerShriekModulePullback_map_id_op F J O a G
  map_comp := fiberLowerShriekModulePullback_map_comp_op F J O a G

/-- The value of `fiberLowerShriekModulePullback` at `n` is `g_{n!}(a_n^* G)`. -/
theorem fiberLowerShriekModulePullback_obj (n : SimplexCategory) :
    (fiberLowerShriekModulePullback F J O a G).obj (op n) =
      (fiberModuleLowerShriek F J O n).obj
        (((fiberStageMorphism F J O n).comp a).modulePullback.obj G) :=
  sorry

/-- The source face map `d_i : g_{(n+1)!}(a_{n+1}^* G) ⟶ g_{n!}(a_n^* G)` in case B. -/
def fiberModulePullbackFace (n : ℕ) (i : Fin (n + 2)) :
    (fiberLowerShriekModulePullback F J O a G).obj (op ⦋n + 1⦌) ⟶
      (fiberLowerShriekModulePullback F J O a G).obj (op ⦋n⦌) :=
  (fiberLowerShriekModulePullback F J O a G).δ i

/-- The face map `fiberModulePullbackFace i` is the simplicial operator `δ i`. -/
theorem fiberModulePullbackFace_eq (n : ℕ) (i : Fin (n + 2)) :
    fiberModulePullbackFace F J O a G n i =
      (fiberLowerShriekModulePullback F J O a G).δ i :=
  sorry

/-- The component of the case B augmentation `g_{n!}(a_n^* G) ⟶ a^* G` at a simplex `n`. -/
def fiberModulePullbackAugmented_hom_app (n : SimplexCategoryᵒᵖ) :
    (fiberLowerShriekModulePullback F J O a G).obj n ⟶ a.modulePullback.obj G :=
  ((fiberModuleLowerShriek.adjunction F J O n.unop).homEquiv
      (((fiberStageMorphism F J O n.unop).comp a).modulePullback.obj G)
      (a.modulePullback.obj G)).symm
    ((fiberRestrictModulePullbackIso F J O a G n.unop).inv ≫
      (fiberModuleInverseImageIsoModulePullback F J O n.unop).inv.app
        (a.modulePullback.obj G))

/-- Naturality of the degreewise case B augmentation `g_{n!}(a_n^* G) ⟶ a^* G`. -/
theorem fiberModulePullbackAugmented_hom_naturality :
    ∀ ⦃n m : SimplexCategoryᵒᵖ⦄ (f : n ⟶ m),
      (fiberLowerShriekModulePullback F J O a G).map f ≫
          fiberModulePullbackAugmented_hom_app F J O a G m =
        fiberModulePullbackAugmented_hom_app F J O a G n ≫
          ((SimplicialObject.const _).obj (a.modulePullback.obj G)).map f :=
  sorry

/-- The natural transformation `n ↦ g_{n!}(a_n^* G) ⟶ const (a^* G)` in case B. -/
def fiberModulePullbackAugmented_hom :
    fiberLowerShriekModulePullback F J O a G ⟶
      (SimplicialObject.const _).obj (a.modulePullback.obj G) where
  app := fiberModulePullbackAugmented_hom_app F J O a G
  naturality := fiberModulePullbackAugmented_hom_naturality F J O a G

/-- The augmented simplicial object of `g_{n!}(a_n^* G)` over `a^* G` in case B. -/
def fiberModulePullbackAugmented : SimplicialObject.Augmented (SheafOfModules.{w} O) where
  left := fiberLowerShriekModulePullback F J O a G
  right := a.modulePullback.obj G
  hom := fiberModulePullbackAugmented_hom F J O a G

/-- The alternating-face chain complex
`… → g_{2!}(a_2^* G) → g_{1!}(a_1^* G) → g_{0!}(a_0^* G)` in case B. -/
abbrev fiberModulePullbackComplex : ChainComplex (SheafOfModules.{w} O) ℕ :=
  (alternatingFaceMapComplex _).obj
    (SimplicialObject.Augmented.drop.obj (fiberModulePullbackAugmented F J O a G))

/-- Degree `n` of `fiberModulePullbackComplex` is the sheaf of modules `g_{n!}(a_n^* G)`. -/
theorem fiberModulePullbackComplex_X (n : ℕ) :
    (fiberModulePullbackComplex F J O a G).X n =
      (fiberModuleLowerShriek F J O ⦋n⦌).obj
        (((fiberStageMorphism F J O ⦋n⦌).comp a).modulePullback.obj G) :=
  sorry

/-- Differentials of `fiberModulePullbackComplex` are the alternating sums of face maps. -/
theorem fiberModulePullbackComplex_d_eq (n : ℕ) :
    (fiberModulePullbackComplex F J O a G).d (n + 1) n =
      ∑ i : Fin (n + 2),
        (-1 : ℤ) ^ (i : ℕ) • fiberModulePullbackFace F J O a G n i :=
  sorry

/-- The canonical chain-map augmentation from `fiberModulePullbackComplex` to `a^* G`
concentrated in degree zero. -/
def fiberModulePullbackAugmentation :
    fiberModulePullbackComplex F J O a G ⟶
      (ChainComplex.single₀ _).obj (a.modulePullback.obj G) :=
  AlternatingFaceMapComplex.ε.app (fiberModulePullbackAugmented F J O a G)

/-- The degree-zero component of `fiberModulePullbackAugmentation` is the simplicial
augmentation at `⦋0⦌`. -/
theorem fiberModulePullbackAugmentation_f_zero :
    (fiberModulePullbackAugmentation F J O a G).f 0 =
      (fiberModulePullbackAugmented F J O a G).hom.app (op ⦋0⦌) :=
  sorry

end CategoryTheory.Grothendieck
