/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import Mathlib.Algebra.Category.ModuleCat.Sheaf.Abelian
public import Mathlib.Algebra.Homology.QuasiIso
public import Mathlib.AlgebraicTopology.AlternatingFaceMapComplex
public import Mathlib.CategoryTheory.Adjunction.CompositionIso
public import stacks_project.Chap85.Lemma_85_6_1_LowerShriek

/-!
# Alternating-face complex of `g_{n!}(a_n^* G)` on a morphism diagram of sites

In Situation 85.3.3 case A, with a morphism of ringed topoi
`a : (Sh(C_total), O) ⟶ (Sh(D), O_D)`, the simplicial sheaf of `O`-modules
`n ↦ g_{n!}(a_n^* G)` on the total site, its augmentation to `a^* G`, and the
associated alternating-face chain complex. Here `g_{n!}` is as in Lemma 85.6.1.
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits Opposite Functor AlgebraicTopology
open HomologicalComplex RingedSite
open scoped Simplicial

noncomputable section

universe u v w uD vD

namespace CategoryTheory.SimplicialSites

variable (C : SimplexCategory ⥤ Cat.{v, u}) (J : ∀ n, Precoverage (C.obj n))
variable [∀ n, HasWeakSheafify (J n).toGrothendieck (Type w)]
variable [∀ (m n : SimplexCategory) (φ : m ⟶ n) (P : (C.obj m)ᵒᵖ ⥤ Type w),
    ((C.map φ).toFunctor).op.HasLeftKanExtension P]
variable [IsMorphismDiagram C J]
variable (O : Sheaf (topology C J) RingCat.{w})
variable [(topology C J).HasSheafCompose (forget RingCat.{w})]
variable [∀ n, ((J n).toGrothendieck).HasSheafCompose (forget RingCat.{w})]
variable [(topology C J).HasSheafCompose (forget₂ RingCat.{w} AddCommGrpCat.{w})]
variable [∀ n, ((J n).toGrothendieck).HasSheafCompose (forget₂ RingCat.{w} AddCommGrpCat.{w})]
variable [∀ n, HasSheafify ((J n).toGrothendieck) (Type w)]
variable [∀ n, ∀ P : (C.obj n)ᵒᵖ ⥤ Type w,
    (ofStage C n).op.HasPointwiseRightKanExtension P]
variable [HasWeakSheafify (topology C J) (Type w)]
variable [∀ n, (SheafOfModules.restrictScalars.{w}
    (stageMorphism C J O n).structureMap).IsRightAdjoint]
variable [∀ {m n : SimplexCategory} (φ : m ⟶ n),
    (SheafOfModules.restrictScalars.{w} (ringedToposMap C J O φ).structureMap).IsRightAdjoint]
variable [∀ n, HasWeakSheafify (J n).toGrothendieck AddCommGrpCat.{w}]
variable [HasWeakSheafify (topology C J) AddCommGrpCat.{w}]
variable [∀ n, HasSheafify ((J n).toGrothendieck) AddCommGrpCat.{w}]
variable [HasSheafify (topology C J) AddCommGrpCat.{w}]
variable [∀ n, ((J n).toGrothendieck).WEqualsLocallyBijective AddCommGrpCat.{w}]
variable [(topology C J).WEqualsLocallyBijective AddCommGrpCat.{w}]
variable {D : RingedSite.{uD, vD, w}}
variable [D.siteTopology.HasSheafCompose (forget RingCat.{w})]
variable (a : ToposHom (totalRingedSite C J O) D)
variable [(SheafOfModules.restrictScalars.{w} a.structureMap).IsRightAdjoint]
variable [∀ n, (SheafOfModules.restrictScalars.{w}
    ((stageMorphism C J O n).comp a).structureMap).IsRightAdjoint]
variable (G : SheafOfModules.{w} D.structureSheaf)

/-- Reconstruct a module morphism from an underlying type-valued sheaf map. -/
def moduleHomOfUnderlying.{uY, vY} {Y : RingedSite.{uY, vY, w}}
    [Y.siteTopology.HasSheafCompose (forget RingCat.{w})]
    {M N : SheafOfModules.{w} Y.structureSheaf}
    (α : (Sheaf.InternalModule.ToInternal.underlying Y.structureSheaf).obj M ⟶
      (Sheaf.InternalModule.ToInternal.underlying Y.structureSheaf).obj N) :
    M ⟶ N :=
  Sheaf.InternalModule.homOfUnderlying Y.structureSheaf α sorry sorry

/-- Lift an underlying-sheaf isomorphism of module functors to a module-functor isomorphism. -/
def moduleIsoOfUnderlying.{uX, vX, uY, vY}
    {X : RingedSite.{uX, vX, w}} {Y : RingedSite.{uY, vY, w}}
    [X.siteTopology.HasSheafCompose (forget RingCat.{w})]
    [Y.siteTopology.HasSheafCompose (forget RingCat.{w})]
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
def stageModulePushforwardCompUnderlyingIso (n : SimplexCategory) :
    ((stageMorphism C J O n).modulePushforward ⋙ a.modulePushforward) ⋙
      Sheaf.InternalModule.ToInternal.underlying D.structureSheaf ≅
      ((stageMorphism C J O n).comp a).modulePushforward ⋙
        Sheaf.InternalModule.ToInternal.underlying D.structureSheaf :=
  Functor.associator _ _ _ ≪≫
    Functor.isoWhiskerLeft (stageMorphism C J O n).modulePushforward
      (ToposHom.ModulePushforward.forgetIso a) ≪≫
    (Functor.associator _ _ _).symm ≪≫
    Functor.isoWhiskerRight (ToposHom.ModulePushforward.forgetIso (stageMorphism C J O n))
      a.toTopos.pushforward ≪≫
    Functor.associator _ _ _ ≪≫
    (ToposHom.ModulePushforward.forgetIso ((stageMorphism C J O n).comp a)).symm

/-- Module pushforwards along `g_n` and `a` compose as `(g_n then a)_*`. -/
def stageModulePushforwardCompIso (n : SimplexCategory) :
    (stageMorphism C J O n).modulePushforward ⋙ a.modulePushforward ≅
      ((stageMorphism C J O n).comp a).modulePushforward :=
  moduleIsoOfUnderlying (stageModulePushforwardCompUnderlyingIso C J O a n)

/-- Identity-on-underlying identification of the degree-`n` restriction `g_n^*(a^* G)`
with `a_n^* G`. -/
def restrictModulePullbackIso (n : SimplexCategory) :
    (stageMorphism C J O n).modulePullback.obj (a.modulePullback.obj G) ≅
      ((stageMorphism C J O n).comp a).modulePullback.obj G :=
  (Adjunction.leftAdjointCompIso a.moduleAdjunction
      (stageMorphism C J O n).moduleAdjunction
      ((stageMorphism C J O n).comp a).moduleAdjunction
      (stageModulePushforwardCompIso C J O a n)).app G

/-- `restrictModulePullbackIso` is the component of the left-adjoint composition comparison. -/
theorem restrictModulePullbackIso_eq (n : SimplexCategory) :
    restrictModulePullbackIso C J O a G n =
      (Adjunction.leftAdjointCompIso a.moduleAdjunction
          (stageMorphism C J O n).moduleAdjunction
          ((stageMorphism C J O n).comp a).moduleAdjunction
          (stageModulePushforwardCompIso C J O a n)).app G :=
  sorry

/-- Continuous-site comparison `f_φ^*(a_n^* G) ⟶ g_m^*(a^* G)` from the mate of
`stageInclusionWhisker`. -/
def modulePullbackStageCompAux {n m : SimplexCategory} (φ : n ⟶ m) :
    (ringedToposMap_pullback C J O φ).obj
      (((stageMorphism C J O n).comp a).modulePullback.obj G) ⟶
      (Cocontinuous.moduleInverseImage (ofStage C m) O).obj (a.modulePullback.obj G) :=
  ((SheafOfModules.pullbackPushforwardAdjunction
      (ringedToposMapDirectStructure C J O φ)).homEquiv
      (((stageMorphism C J O n).comp a).modulePullback.obj G)
      ((Cocontinuous.moduleInverseImage (ofStage C m) O).obj
        (a.modulePullback.obj G))).symm
    ((restrictModulePullbackIso C J O a G n).inv ≫
      (moduleInverseImageIsoModulePullback C J O n).inv.app
        (a.modulePullback.obj G) ≫
      (SheafOfModules.pushforwardNatTrans (𝟙 (componentRingSheaf C J O n))
          (stageInclusionWhisker C φ)).app (a.modulePullback.obj G) ≫
      (SheafOfModules.pushforwardComp (ringedToposMapDirectStructure C J O φ)
          (𝟙 (componentRingSheaf C J O m))).inv.app (a.modulePullback.obj G))

/-- Restriction `f_φ^*(a_n^* G) ⟶ a_m^* G` along the simplicial 2-cell. -/
def modulePullbackStageComp {n m : SimplexCategory} (φ : n ⟶ m) :
    (ringedToposMap C J O φ).modulePullback.obj
      (((stageMorphism C J O n).comp a).modulePullback.obj G) ⟶
      ((stageMorphism C J O m).comp a).modulePullback.obj G :=
  (ringedToposMap_pullbackIso C J O φ).inv.app
      (((stageMorphism C J O n).comp a).modulePullback.obj G) ≫
    modulePullbackStageCompAux C J O a G φ ≫
    (moduleInverseImageIsoModulePullback C J O m).hom.app (a.modulePullback.obj G) ≫
    (restrictModulePullbackIso C J O a G m).hom

/-- The comparison `f_φ^*(a_n^* G) ⟶ a_m^* G` is an isomorphism, as
`a_m ∘ f_φ = a_n` on ringed topoi. -/
instance modulePullbackStageComp_isIso {n m : SimplexCategory} (φ : n ⟶ m) :
    IsIso (modulePullbackStageComp C J O a G φ) :=
  sorry

/-- Inverse-image form of `a_m ∘ f_φ = a_n` on modules. -/
def modulePullbackStageCompIso {n m : SimplexCategory} (φ : n ⟶ m) :
    ((stageMorphism C J O m).comp a).modulePullback.obj G ≅
      (ringedToposMap C J O φ).modulePullback.obj
        (((stageMorphism C J O n).comp a).modulePullback.obj G) :=
  (asIso (modulePullbackStageComp C J O a G φ)).symm

/-- The structure map `g_{m!}(a_m^* G) ⟶ g_{n!}(a_n^* G)` induced by a simplex
operator `φ : n ⟶ m`. -/
def lowerShriekModulePullback_map {n m : SimplexCategory} (φ : n ⟶ m) :
    (moduleLowerShriek C J O m).obj
      (((stageMorphism C J O m).comp a).modulePullback.obj G) ⟶
    (moduleLowerShriek C J O n).obj
      (((stageMorphism C J O n).comp a).modulePullback.obj G) :=
  ((moduleLowerShriek.adjunction C J O m).homEquiv
      (((stageMorphism C J O m).comp a).modulePullback.obj G)
      ((moduleLowerShriek C J O n).obj
        (((stageMorphism C J O n).comp a).modulePullback.obj G))).symm
    ((modulePullbackStageCompIso C J O a G φ).hom ≫
      moduleLowerShriek_component C J O φ
        (((stageMorphism C J O n).comp a).modulePullback.obj G) ≫
      (moduleInverseImageIsoModulePullback C J O m).inv.app
        ((moduleLowerShriek C J O n).obj
          (((stageMorphism C J O n).comp a).modulePullback.obj G)))

/-- Identity simplex operators induce identity structure maps of
`n ↦ g_{n!}(a_n^* G)`. -/
theorem lowerShriekModulePullback_map_id (n : SimplexCategory) :
    lowerShriekModulePullback_map C J O a G (𝟙 n) =
      𝟙 ((moduleLowerShriek C J O n).obj
        (((stageMorphism C J O n).comp a).modulePullback.obj G)) :=
  sorry

/-- Structure maps of `n ↦ g_{n!}(a_n^* G)` are functorial in simplex operators. -/
theorem lowerShriekModulePullback_map_comp {l n m : SimplexCategory}
    (ψ : l ⟶ n) (φ : n ⟶ m) :
    lowerShriekModulePullback_map C J O a G (ψ ≫ φ) =
      lowerShriekModulePullback_map C J O a G φ ≫
        lowerShriekModulePullback_map C J O a G ψ :=
  sorry

/-- Opposite identity operators act as identity maps of `n ↦ g_{n!}(a_n^* G)`. -/
theorem lowerShriekModulePullback_map_id_op (n : SimplexCategoryᵒᵖ) :
    lowerShriekModulePullback_map C J O a G (𝟙 n.unop) =
      𝟙 ((moduleLowerShriek C J O n.unop).obj
        (((stageMorphism C J O n.unop).comp a).modulePullback.obj G)) :=
  sorry

/-- Opposite composition of simplex operators acts as composition of structure maps. -/
theorem lowerShriekModulePullback_map_comp_op {n m p : SimplexCategoryᵒᵖ}
    (f : n ⟶ m) (g : m ⟶ p) :
    lowerShriekModulePullback_map C J O a G (f ≫ g).unop =
      lowerShriekModulePullback_map C J O a G f.unop ≫
        lowerShriekModulePullback_map C J O a G g.unop :=
  sorry

/-- The simplicial sheaf of `O`-modules `n ↦ g_{n!}(a_n^* G)` on the total site. -/
def lowerShriekModulePullback : SimplicialObject (SheafOfModules.{w} O) where
  obj n :=
    (moduleLowerShriek C J O n.unop).obj
      (((stageMorphism C J O n.unop).comp a).modulePullback.obj G)
  map f := lowerShriekModulePullback_map C J O a G f.unop
  map_id := lowerShriekModulePullback_map_id_op C J O a G
  map_comp := lowerShriekModulePullback_map_comp_op C J O a G

/-- The value of `lowerShriekModulePullback` at `n` is `g_{n!}(a_n^* G)`. -/
theorem lowerShriekModulePullback_obj (n : SimplexCategory) :
    (lowerShriekModulePullback C J O a G).obj (op n) =
      (moduleLowerShriek C J O n).obj
        (((stageMorphism C J O n).comp a).modulePullback.obj G) :=
  sorry

/-- The source face map `d_i : g_{(n+1)!}(a_{n+1}^* G) ⟶ g_{n!}(a_n^* G)`. -/
def modulePullbackFace (n : ℕ) (i : Fin (n + 2)) :
    (lowerShriekModulePullback C J O a G).obj (op ⦋n + 1⦌) ⟶
      (lowerShriekModulePullback C J O a G).obj (op ⦋n⦌) :=
  (lowerShriekModulePullback C J O a G).δ i

/-- The face map `modulePullbackFace i` is the simplicial operator `δ i`. -/
theorem modulePullbackFace_eq (n : ℕ) (i : Fin (n + 2)) :
    modulePullbackFace C J O a G n i = (lowerShriekModulePullback C J O a G).δ i :=
  sorry

/-- The component of the augmentation `g_{n!}(a_n^* G) ⟶ a^* G` at a simplex `n`. -/
def modulePullbackAugmented_hom_app (n : SimplexCategoryᵒᵖ) :
    (lowerShriekModulePullback C J O a G).obj n ⟶ a.modulePullback.obj G :=
  ((moduleLowerShriek.adjunction C J O n.unop).homEquiv
      (((stageMorphism C J O n.unop).comp a).modulePullback.obj G)
      (a.modulePullback.obj G)).symm
    ((restrictModulePullbackIso C J O a G n.unop).inv ≫
      (moduleInverseImageIsoModulePullback C J O n.unop).inv.app
        (a.modulePullback.obj G))

/-- Naturality of the degreewise augmentation `g_{n!}(a_n^* G) ⟶ a^* G`. -/
theorem modulePullbackAugmented_hom_naturality :
    ∀ ⦃n m : SimplexCategoryᵒᵖ⦄ (f : n ⟶ m),
      (lowerShriekModulePullback C J O a G).map f ≫
          modulePullbackAugmented_hom_app C J O a G m =
        modulePullbackAugmented_hom_app C J O a G n ≫
          ((SimplicialObject.const _).obj (a.modulePullback.obj G)).map f :=
  sorry

/-- The natural transformation `n ↦ g_{n!}(a_n^* G) ⟶ const (a^* G)`. -/
def modulePullbackAugmented_hom :
    lowerShriekModulePullback C J O a G ⟶
      (SimplicialObject.const _).obj (a.modulePullback.obj G) where
  app := modulePullbackAugmented_hom_app C J O a G
  naturality := modulePullbackAugmented_hom_naturality C J O a G

/-- The augmented simplicial object of `g_{n!}(a_n^* G)` over `a^* G`. -/
def modulePullbackAugmented : SimplicialObject.Augmented (SheafOfModules.{w} O) where
  left := lowerShriekModulePullback C J O a G
  right := a.modulePullback.obj G
  hom := modulePullbackAugmented_hom C J O a G

/-- The alternating-face chain complex
`… → g_{2!}(a_2^* G) → g_{1!}(a_1^* G) → g_{0!}(a_0^* G)`. -/
abbrev modulePullbackComplex : ChainComplex (SheafOfModules.{w} O) ℕ :=
  (alternatingFaceMapComplex _).obj
    (SimplicialObject.Augmented.drop.obj (modulePullbackAugmented C J O a G))

/-- Degree `n` of `modulePullbackComplex` is the sheaf of modules `g_{n!}(a_n^* G)`. -/
theorem modulePullbackComplex_X (n : ℕ) :
    (modulePullbackComplex C J O a G).X n =
      (moduleLowerShriek C J O ⦋n⦌).obj
        (((stageMorphism C J O ⦋n⦌).comp a).modulePullback.obj G) :=
  sorry

/-- Differentials of `modulePullbackComplex` are the alternating sums of face maps. -/
theorem modulePullbackComplex_d_eq (n : ℕ) :
    (modulePullbackComplex C J O a G).d (n + 1) n =
      ∑ i : Fin (n + 2), (-1 : ℤ) ^ (i : ℕ) • modulePullbackFace C J O a G n i :=
  sorry

/-- The canonical chain-map augmentation from `modulePullbackComplex` to `a^* G`
concentrated in degree zero. -/
def modulePullbackAugmentation :
    modulePullbackComplex C J O a G ⟶
      (ChainComplex.single₀ _).obj (a.modulePullback.obj G) :=
  AlternatingFaceMapComplex.ε.app (modulePullbackAugmented C J O a G)

/-- The degree-zero component of `modulePullbackAugmentation` is the simplicial
augmentation at `⦋0⦌`. -/
theorem modulePullbackAugmentation_f_zero :
    (modulePullbackAugmentation C J O a G).f 0 =
      (modulePullbackAugmented C J O a G).hom.app (op ⦋0⦌) :=
  sorry

end CategoryTheory.SimplicialSites
