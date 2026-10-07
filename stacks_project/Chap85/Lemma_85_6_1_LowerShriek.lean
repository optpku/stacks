module

public import ReasLib.AlgebraicGeometry.RingedSite.Topos.ModuleAdjunction
public import stacks_project.Chap85.Lemma_85_6_1_Ringed

/-!
# Module lower shriek along a ringed stage inclusion

The left adjoint `g_{n!}` of module pullback along `g_n`, and the identification of
its restriction to `C_m` with the coproduct of `f_φ^* G` over simplex operators
`φ : n ⟶ m`.
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits Opposite Functor
open RingedSite
open Sheaf.InternalModule

noncomputable section

universe u v w

namespace CategoryTheory.SimplicialSites

variable (C : SimplexCategory ⥤ Cat.{v, u}) (J : ∀ n, Precoverage (C.obj n))
variable [∀ n, HasWeakSheafify (J n).toGrothendieck (Type w)]
variable [∀ (m n : SimplexCategory) (φ : m ⟶ n) (P : (C.obj m)ᵒᵖ ⥤ Type w),
    ((C.map φ).toFunctor).op.HasLeftKanExtension P]
variable [IsMorphismDiagram C J]
variable (O : Sheaf (topology C J) RingCat.{w})
variable [(topology C J).HasSheafCompose (forget RingCat.{w})]
variable [∀ n, ((J n).toGrothendieck).HasSheafCompose (forget RingCat.{w})]
variable [∀ n, HasSheafify ((J n).toGrothendieck) (Type w)]
variable [∀ n, ∀ P : (C.obj n)ᵒᵖ ⥤ Type w,
    (ofStage C n).op.HasPointwiseRightKanExtension P]
variable [HasWeakSheafify (topology C J) (Type w)]

/-- Module lower shriek `g_{n!}` along the degree-`n` inclusion, as in Lemma 18.41.1. -/
abbrev moduleLowerShriek (n : SimplexCategory) :
    SheafOfModules.{w} (componentRingSheaf C J O n) ⥤ SheafOfModules.{w} O :=
  Cocontinuous.moduleLowerShriek (ofStage C n) O

/-- `moduleLowerShriek` is the ReasLib lower shriek along `ofStage C n`. -/
theorem moduleLowerShriek_eq (n : SimplexCategory) :
    moduleLowerShriek C J O n = Cocontinuous.moduleLowerShriek (ofStage C n) O :=
  sorry

/-- The canonical adjunction `g_{n!} ⊣` module inverse image along `ofStage C n`. -/
def moduleLowerShriek.adjunction (n : SimplexCategory) :
    moduleLowerShriek C J O n ⊣ Cocontinuous.moduleInverseImage (ofStage C n) O :=
  Cocontinuous.moduleLowerShriek.adjunction (ofStage C n) O

/-- The adjunction is the ReasLib lower-shriek/inverse-image adjunction along `ofStage`. -/
theorem moduleLowerShriek.adjunction_eq (n : SimplexCategory) :
    moduleLowerShriek.adjunction C J O n =
      Cocontinuous.moduleLowerShriek.adjunction (ofStage C n) O :=
  sorry

variable [∀ n, (SheafOfModules.restrictScalars.{w}
    (stageMorphism C J O n).structureMap).IsRightAdjoint]
variable [∀ {m n : SimplexCategory} (φ : m ⟶ n),
    (SheafOfModules.restrictScalars.{w} (ringedToposMap C J O φ).structureMap).IsRightAdjoint]

/-- Underlying type-valued sheaf of module inverse image along `ofStage C n`. -/
def moduleInverseImage_underlyingIso (n : SimplexCategory)
    (M : SheafOfModules.{w} O) :
    (Sheaf.InternalModule.ToInternal.underlying (componentRingSheaf C J O n)).obj
      ((Cocontinuous.moduleInverseImage (ofStage C n) O).obj M) ≅
      ((ofStage C n).sheafPushforwardContinuous (Type w)
        (J n).toGrothendieck (topology C J)).obj
        ((Sheaf.InternalModule.ToInternal.underlying O).obj M) :=
  (fullyFaithfulSheafToPresheaf ((J n).toGrothendieck) (Type w)).preimageIso <|
    NatIso.ofComponents (fun _ ↦ Iso.refl _) sorry

/-- Restriction of scalars along the structure map of `g_n` does not change the
underlying type-valued sheaf of `g_n^* M`. -/
def modulePullback_restrictScalars_underlyingIso (n : SimplexCategory)
    (M : SheafOfModules.{w} O) :
    (Sheaf.InternalModule.ToInternal.underlying (componentRingSheaf C J O n)).obj
      ((stageMorphism C J O n).modulePullback.obj M) ≅
      (Sheaf.InternalModule.ToInternal.underlying
          ((stageMorphism C J O n).toTopos.ringInverseImage.obj O)).obj
        ((SheafOfModules.restrictScalars (stageMorphism C J O n).structureMap).obj
          ((stageMorphism C J O n).modulePullback.obj M)) :=
  (fullyFaithfulSheafToPresheaf ((J n).toGrothendieck) (Type w)).preimageIso <|
    NatIso.ofComponents (fun _ ↦ Iso.refl _) sorry

/-- The scalar-extension unit comparing geometric inverse image with `g_n^*`. -/
def modulePullback_scalarUnit (n : SimplexCategory)
    (M : SheafOfModules.{w} O) :
    ((stageMorphism C J O n).toTopos.moduleInverseImage O).obj M ⟶
      (SheafOfModules.restrictScalars (stageMorphism C J O n).structureMap).obj
        ((stageMorphism C J O n).modulePullback.obj M) :=
  (SheafOfModules.ChangeOfRings.extendRestrictAdjunction
      (stageMorphism C J O n).structureMap).unit.app
    (((stageMorphism C J O n).toTopos.moduleInverseImage O).obj M)

/-- The scalar-extension unit is an isomorphism, since the structure map of `g_n` is
the identity comparison. -/
instance modulePullback_scalarUnit_isIso (n : SimplexCategory)
    (M : SheafOfModules.{w} O) :
    IsIso (modulePullback_scalarUnit C J O n M) :=
  sorry

/-- The cocontinuous-to-continuous comparison along `ofStage C n` is an isomorphism. -/
instance ofStage_cocontinuousPullback_comparison_isIso (n : SimplexCategory) :
    IsIso (Functor.CocontinuousPullback.comparison (ofStage C n)
      (J n).toGrothendieck (topology C J)) :=
  Functor.CocontinuousPullback.comparison.isIso (ofStage C n)
    (J n).toGrothendieck (topology C J)

/-- Components of the cocontinuous-to-continuous comparison are isomorphisms. -/
instance ofStage_cocontinuousPullback_comparison_app_isIso (n : SimplexCategory)
    (M : Sheaf (topology C J) (Type w)) :
    IsIso ((Functor.CocontinuousPullback.comparison (ofStage C n)
        (J n).toGrothendieck (topology C J)).app M) :=
  sorry

/-- Underlying type-valued sheaf of `g_n^*`. -/
def modulePullback_underlyingIso (n : SimplexCategory)
    (M : SheafOfModules.{w} O) :
    (Sheaf.InternalModule.ToInternal.underlying (componentRingSheaf C J O n)).obj
      ((stageMorphism C J O n).modulePullback.obj M) ≅
      ((ofStage C n).sheafPushforwardContinuous (Type w)
        (J n).toGrothendieck (topology C J)).obj
        ((Sheaf.InternalModule.ToInternal.underlying O).obj M) :=
  modulePullback_restrictScalars_underlyingIso C J O n M ≪≫
    (asIso
      ((Sheaf.InternalModule.ToInternal.underlying
          ((stageMorphism C J O n).toTopos.ringInverseImage.obj O)).map
        (modulePullback_scalarUnit C J O n M))).symm ≪≫
    ((stageMorphism C J O n).toTopos.moduleInverseImageForgetIso O).app M ≪≫
    (asIso
      (Functor.CocontinuousPullback.comparison (ofStage C n)
        (J n).toGrothendieck (topology C J))).app
      ((Sheaf.InternalModule.ToInternal.underlying O).obj M)

/-- The comparison `g_n^* ⟶` module inverse image, lifting
`CocontinuousPullback.comparison`. -/
def modulePullbackToModuleInverseImage (n : SimplexCategory) :
    (stageMorphism C J O n).modulePullback ⟶
      Cocontinuous.moduleInverseImage (ofStage C n) O where
  app M :=
    Sheaf.InternalModule.homOfUnderlying (componentRingSheaf C J O n)
      ((modulePullback_underlyingIso C J O n M).hom ≫
        (moduleInverseImage_underlyingIso C J O n M).inv)
      sorry sorry
  naturality := sorry

/-- The comparison `modulePullbackToModuleInverseImage` is an isomorphism. -/
instance modulePullbackToModuleInverseImage_isIso (n : SimplexCategory) :
    IsIso (modulePullbackToModuleInverseImage C J O n) :=
  sorry

/-- Module inverse image along `ofStage C n` is isomorphic to `g_n^*`. -/
def moduleInverseImageIsoModulePullback (n : SimplexCategory) :
    Cocontinuous.moduleInverseImage (ofStage C n) O ≅
      (stageMorphism C J O n).modulePullback :=
  (asIso (modulePullbackToModuleInverseImage C J O n)).symm

/-- The forward map of `moduleInverseImageIsoModulePullback` is the inverse of the
cocontinuous-to-continuous comparison lift. -/
theorem moduleInverseImageIsoModulePullback_hom (n : SimplexCategory) :
    (moduleInverseImageIsoModulePullback C J O n).hom =
      (asIso (modulePullbackToModuleInverseImage C J O n)).inv :=
  sorry

/-- Continuous-site module pushforward along `u_φ` with the direct-image form of `O(φ)`. -/
abbrev ringedToposMap_pushforward {m n : SimplexCategory} (φ : m ⟶ n) :
    SheafOfModules.{w} (componentRingSheaf C J O n) ⥤
      SheafOfModules.{w} (componentRingSheaf C J O m) :=
  SheafOfModules.pushforward (ringedToposMapDirectStructure C J O φ)

/-- Underlying type-valued sheaf of continuous-site module pushforward along `u_φ`. -/
def ringedToposMap_pushforward_underlyingIso {m n : SimplexCategory} (φ : m ⟶ n)
    (M : SheafOfModules.{w} (componentRingSheaf C J O n)) :
    (Sheaf.InternalModule.ToInternal.underlying (componentRingSheaf C J O m)).obj
      ((ringedToposMap_pushforward C J O φ).obj M) ≅
      ((C.map φ).toFunctor.sheafPushforwardContinuous (Type w)
        (J m).toGrothendieck (J n).toGrothendieck).obj
        ((Sheaf.InternalModule.ToInternal.underlying
          (componentRingSheaf C J O n)).obj M) :=
  (fullyFaithfulSheafToPresheaf ((J m).toGrothendieck) (Type w)).preimageIso <|
    NatIso.ofComponents (fun _ ↦ Iso.refl _) sorry

/-- Continuous-site module pushforward along `u_φ` is isomorphic to `f_φ_*`. -/
def ringedToposMap_pushforwardIso {m n : SimplexCategory} (φ : m ⟶ n) :
    ringedToposMap_pushforward C J O φ ≅ (ringedToposMap C J O φ).modulePushforward :=
  NatIso.ofComponents
    (fun M ↦
      { hom :=
          Sheaf.InternalModule.homOfUnderlying (componentRingSheaf C J O m)
            ((ringedToposMap_pushforward_underlyingIso C J O φ M).hom ≫
              (ToposHom.ModulePushforward.forgetIso
                  (ringedToposMap C J O φ)).inv.app M)
            sorry sorry
        inv :=
          Sheaf.InternalModule.homOfUnderlying (componentRingSheaf C J O m)
            ((ToposHom.ModulePushforward.forgetIso
                  (ringedToposMap C J O φ)).hom.app M ≫
              (ringedToposMap_pushforward_underlyingIso C J O φ M).inv)
            sorry sorry
        hom_inv_id := sorry
        inv_hom_id := sorry })
    sorry

/-- Direct image of modules along `f_φ` is a right adjoint. -/
instance ringedToposMap_modulePushforward_isRightAdjoint {m n : SimplexCategory}
    (φ : m ⟶ n) :
    ((ringedToposMap C J O φ).modulePushforward).IsRightAdjoint :=
  (ringedToposMap C J O φ).moduleAdjunction.isRightAdjoint

/-- Continuous-site module pushforward along `u_φ` is a right adjoint. -/
instance ringedToposMap_pushforward_isRightAdjoint {m n : SimplexCategory}
    (φ : m ⟶ n) :
    (ringedToposMap_pushforward C J O φ).IsRightAdjoint :=
  Functor.isRightAdjoint_of_iso (ringedToposMap_pushforwardIso C J O φ).symm

/-- Continuous-site module pullback along `u_φ` with the direct-image form of `O(φ)`. -/
abbrev ringedToposMap_pullback {m n : SimplexCategory} (φ : m ⟶ n) :
    SheafOfModules.{w} (componentRingSheaf C J O m) ⥤
      SheafOfModules.{w} (componentRingSheaf C J O n) :=
  SheafOfModules.pullback (ringedToposMapDirectStructure C J O φ)

/-- Continuous-site module pullback along `u_φ` is isomorphic to `f_φ^*`. -/
def ringedToposMap_pullbackIso {m n : SimplexCategory} (φ : m ⟶ n) :
    ringedToposMap_pullback C J O φ ≅ (ringedToposMap C J O φ).modulePullback :=
  Adjunction.leftAdjointUniq
    (SheafOfModules.pullbackPushforwardAdjunction
      (ringedToposMapDirectStructure C J O φ))
    ((ringedToposMap C J O φ).moduleAdjunction.ofNatIsoRight
      (ringedToposMap_pushforwardIso C J O φ).symm)

/-- The canonical component map `f_φ^* G ⟶ (g_{n!} G)_m` in continuous-site form,
using the lower-shriek unit and the mate of `stageInclusionWhisker`. -/
def moduleLowerShriek_componentAux {n m : SimplexCategory} (φ : n ⟶ m)
    (G : SheafOfModules.{w} (componentRingSheaf C J O n)) :
    (ringedToposMap_pullback C J O φ).obj G ⟶
      (Cocontinuous.moduleInverseImage (ofStage C m) O).obj
        ((moduleLowerShriek C J O n).obj G) :=
  ((SheafOfModules.pullbackPushforwardAdjunction
      (ringedToposMapDirectStructure C J O φ)).homEquiv G
      ((Cocontinuous.moduleInverseImage (ofStage C m) O).obj
        ((moduleLowerShriek C J O n).obj G))).symm
    ((moduleLowerShriek.adjunction C J O n).unit.app G ≫
      (SheafOfModules.pushforwardNatTrans (𝟙 (componentRingSheaf C J O n))
          (stageInclusionWhisker C φ)).app
        ((moduleLowerShriek C J O n).obj G) ≫
      (SheafOfModules.pushforwardComp (ringedToposMapDirectStructure C J O φ)
          (𝟙 (componentRingSheaf C J O m))).inv.app
        ((moduleLowerShriek C J O n).obj G))

/-- The canonical component map `f_φ^* G ⟶ (g_{n!} G)_m`. -/
def moduleLowerShriek_component {n m : SimplexCategory} (φ : n ⟶ m)
    (G : SheafOfModules.{w} (componentRingSheaf C J O n)) :
    (ringedToposMap C J O φ).modulePullback.obj G ⟶
      (stageMorphism C J O m).modulePullback.obj ((moduleLowerShriek C J O n).obj G) :=
  (ringedToposMap_pullbackIso C J O φ).inv.app G ≫
    moduleLowerShriek_componentAux C J O φ G ≫
    (moduleInverseImageIsoModulePullback C J O m).hom.app
      ((moduleLowerShriek C J O n).obj G)

/-- The coproduct comparison morphism
`∐_{φ : n ⟶ m} f_φ^* G ⟶ (g_{n!} G)_m`. -/
def moduleLowerShriek_componentBiproductHom (n m : SimplexCategory)
    [HasColimitsOfShape (Discrete (n ⟶ m))
      (SheafOfModules.{w} (componentRingSheaf C J O m))]
    (G : SheafOfModules.{w} (componentRingSheaf C J O n)) :
    (∐ fun φ : n ⟶ m ↦ (ringedToposMap C J O φ).modulePullback.obj G) ⟶
      (stageMorphism C J O m).modulePullback.obj ((moduleLowerShriek C J O n).obj G) :=
  Sigma.desc fun φ ↦ moduleLowerShriek_component C J O φ G

/-- The coproduct comparison is the coproduct of the component maps. -/
theorem moduleLowerShriek_componentBiproductHom_eq (n m : SimplexCategory)
    [HasColimitsOfShape (Discrete (n ⟶ m))
      (SheafOfModules.{w} (componentRingSheaf C J O m))]
    (G : SheafOfModules.{w} (componentRingSheaf C J O n)) :
    moduleLowerShriek_componentBiproductHom C J O n m G =
      Sigma.desc fun φ ↦ moduleLowerShriek_component C J O φ G :=
  sorry

/-- The coproduct comparison morphism is an isomorphism. -/
instance moduleLowerShriek_componentBiproductHom_isIso (n m : SimplexCategory)
    [HasColimitsOfShape (Discrete (n ⟶ m))
      (SheafOfModules.{w} (componentRingSheaf C J O m))]
    (G : SheafOfModules.{w} (componentRingSheaf C J O n)) :
    IsIso (moduleLowerShriek_componentBiproductHom C J O n m G) :=
  sorry

/-- Restriction of `g_{n!} G` to `C_m` is `⊕_{φ : n ⟶ m} f_φ^* G`. -/
def moduleLowerShriek_componentBiproductIso (n m : SimplexCategory)
    [HasColimitsOfShape (Discrete (n ⟶ m))
      (SheafOfModules.{w} (componentRingSheaf C J O m))]
    (G : SheafOfModules.{w} (componentRingSheaf C J O n)) :
    (∐ fun φ : n ⟶ m ↦ (ringedToposMap C J O φ).modulePullback.obj G) ≅
      (stageMorphism C J O m).modulePullback.obj ((moduleLowerShriek C J O n).obj G) :=
  asIso (moduleLowerShriek_componentBiproductHom C J O n m G)

/-- The coproduct inclusion of `f_φ^* G` followed by the comparison is the component map. -/
theorem moduleLowerShriek_componentBiproduct_ι (n m : SimplexCategory)
    [HasColimitsOfShape (Discrete (n ⟶ m))
      (SheafOfModules.{w} (componentRingSheaf C J O m))]
    (G : SheafOfModules.{w} (componentRingSheaf C J O n)) (φ : n ⟶ m) :
    Sigma.ι (fun ψ : n ⟶ m ↦ (ringedToposMap C J O ψ).modulePullback.obj G) φ ≫
      (moduleLowerShriek_componentBiproductIso C J O n m G).hom =
      moduleLowerShriek_component C J O φ G :=
  sorry

end CategoryTheory.SimplicialSites
