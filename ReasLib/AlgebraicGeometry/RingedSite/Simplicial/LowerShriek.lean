module

public import ReasLib.AlgebraicGeometry.RingedSite.Topos.ModuleAdjunction
public import ReasLib.AlgebraicGeometry.RingedSite.Simplicial.Operators
public import ReasLib.AlgebraicGeometry.RingedSite.Topos.Cocontinuous.StructureIso
public import ReasLib.Algebra.Category.ModuleCat.Sheaf.ChangeOfRings.Iso
public import ReasLib.Algebra.Category.ModuleCat.Sheaf.ChangeOfRings.Small

/-!
# Module lower shriek along a ringed stage inclusion

The left adjoint `g_{n!}` of module pullback along `g_n`, and the identification of
its restriction to `C_m` with the coproduct of `f_φ^* G` over simplex operators
`φ : n ⟶ m`.
-/

-- Private laws and component maps remain implementation details of the explicit constructions.
set_option backward.privateInPublic true

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
variable [UnivLE.{max u v, w}]
variable (O : Sheaf (topology C J) RingCat.{w})
variable [(topology C J).HasSheafCompose (forget RingCat.{w})]
variable [∀ n, ((J n).toGrothendieck).HasSheafCompose (forget RingCat.{w})]
variable [∀ n, HasSheafify ((J n).toGrothendieck) (Type w)]
variable [∀ n, ∀ P : (C.obj n)ᵒᵖ ⥤ Type w,
    (ofStage C n).op.HasPointwiseRightKanExtension P]
variable [HasWeakSheafify (topology C J) (Type w)]

/-- Module lower shriek `g_{n!}` along the degree-`n` inclusion. -/
abbrev moduleLowerShriek (n : SimplexCategory) :
    SheafOfModules.{w} (componentRingSheaf C J O n) ⥤ SheafOfModules.{w} O :=
  Cocontinuous.moduleLowerShriek (ofStage C n) O

omit [UnivLE.{max u v, w}] [(topology C J).HasSheafCompose (forget RingCat)] [∀ (n :
  SimplexCategory), (J n).toGrothendieck.HasSheafCompose (forget RingCat)] [∀ (n : SimplexCategory),
  HasSheafify (J n).toGrothendieck (Type w)] [∀ (n : SimplexCategory) (P : (C.obj n : Type u)ᵒᵖ ⥤ Type w),
  (ofStage C n).op.HasPointwiseRightKanExtension P] [HasWeakSheafify (topology C J) (Type w)] in
/-- `moduleLowerShriek` is the lower shriek along `ofStage C n`. -/
theorem moduleLowerShriek_eq (n : SimplexCategory) :
    moduleLowerShriek C J O n = Cocontinuous.moduleLowerShriek (ofStage C n) O :=
  rfl

/-- The canonical adjunction `g_{n!} ⊣` module inverse image along `ofStage C n`. -/
def moduleLowerShriek.adjunction (n : SimplexCategory) :
    moduleLowerShriek C J O n ⊣ Cocontinuous.moduleInverseImage (ofStage C n) O :=
  Cocontinuous.moduleLowerShriek.adjunction (ofStage C n) O

omit [UnivLE.{max u v, w}] [(topology C J).HasSheafCompose (forget RingCat)] [∀ (n :
  SimplexCategory), (J n).toGrothendieck.HasSheafCompose (forget RingCat)] [∀ (n : SimplexCategory),
  HasSheafify (J n).toGrothendieck (Type w)] [∀ (n : SimplexCategory) (P : (C.obj n : Type u)ᵒᵖ ⥤ Type w),
  (ofStage C n).op.HasPointwiseRightKanExtension P] [HasWeakSheafify (topology C J) (Type w)] in
/-- The adjunction is the lower-shriek/inverse-image adjunction along `ofStage`. -/
theorem moduleLowerShriek.adjunction_eq (n : SimplexCategory) :
    moduleLowerShriek.adjunction C J O n =
      Cocontinuous.moduleLowerShriek.adjunction (ofStage C n) O :=
  rfl

/-- The identity component functions commute with presheaf restriction. -/
private theorem moduleInverseImage_underlyingIso_naturality (n : SimplexCategory)
    (M : SheafOfModules.{w} O) :
    let A := (sheafToPresheaf _ (Type w)).obj ((Sheaf.InternalModule.ToInternal.underlying (componentRingSheaf C J O n)).obj
      ((Cocontinuous.moduleInverseImage (ofStage C n) O).obj M))
    let B := (sheafToPresheaf _ (Type w)).obj (((ofStage C n).sheafPushforwardContinuous (Type w)
        (J n).toGrothendieck (topology C J)).obj
        ((Sheaf.InternalModule.ToInternal.underlying O).obj M))
    ∀ {U V} (f : U ⟶ V),
      A.map f ≫ (Iso.refl (A.obj V)).hom =
        (Iso.refl (A.obj U)).hom ≫ B.map f := by
  sorry

/-- Underlying type-valued sheaf of module inverse image along `ofStage C n`. -/
def moduleInverseImage_underlyingIso (n : SimplexCategory)
    (M : SheafOfModules.{w} O) :
    (Sheaf.InternalModule.ToInternal.underlying (componentRingSheaf C J O n)).obj
      ((Cocontinuous.moduleInverseImage (ofStage C n) O).obj M) ≅
      ((ofStage C n).sheafPushforwardContinuous (Type w)
        (J n).toGrothendieck (topology C J)).obj
        ((Sheaf.InternalModule.ToInternal.underlying O).obj M) :=
  (fullyFaithfulSheafToPresheaf ((J n).toGrothendieck) (Type w)).preimageIso <|
    NatIso.ofComponents (fun _ ↦ Iso.refl _) (by
      intro U V f
      exact (moduleInverseImage_underlyingIso_naturality C J O n M) f)

/-- The identity component functions commute with presheaf restriction. -/
private theorem modulePullback_restrictScalars_underlyingIso_naturality (n : SimplexCategory)
    (M : SheafOfModules.{w} O) :
    let A := (sheafToPresheaf _ (Type w)).obj ((Sheaf.InternalModule.ToInternal.underlying (componentRingSheaf C J O n)).obj
      ((stageMorphism C J O n).modulePullback.obj M))
    let B := (sheafToPresheaf _ (Type w)).obj ((Sheaf.InternalModule.ToInternal.underlying
          ((stageMorphism C J O n).toTopos.ringInverseImage.obj O)).obj
        ((SheafOfModules.restrictScalars (stageMorphism C J O n).structureMap).obj
          ((stageMorphism C J O n).modulePullback.obj M)))
    ∀ {U V} (f : U ⟶ V),
      A.map f ≫ (Iso.refl (A.obj V)).hom =
        (Iso.refl (A.obj U)).hom ≫ B.map f := by
  sorry

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
    NatIso.ofComponents (fun _ ↦ Iso.refl _) (by
      intro U V f
      exact (modulePullback_restrictScalars_underlyingIso_naturality C J O n M) f)

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
  (SheafOfModules.ChangeOfRings.extendRestrictUnitIso
    (Cocontinuous.structureMapIso
        (X := componentRingedSite C J O n) (Y := totalRingedSite C J O)
        (ofStage C n) (Iso.refl _))
    (((stageMorphism C J O n).toTopos.moduleInverseImage O).obj M)).isIso_hom

/-- Underlying type-valued sheaf of `g_n^*`. -/
def modulePullback_underlyingIso (n : SimplexCategory)
    (M : SheafOfModules.{w} O) :
    (Sheaf.InternalModule.ToInternal.underlying (componentRingSheaf C J O n)).obj
      ((stageMorphism C J O n).modulePullback.obj M) ≅
      ((ofStage C n).sheafPushforwardContinuous (Type w)
        (J n).toGrothendieck (topology C J)).obj
        ((Sheaf.InternalModule.ToInternal.underlying O).obj M) :=
  modulePullback_restrictScalars_underlyingIso C J O n M ≪≫
    ((ToInternal.underlying
        ((stageMorphism C J O n).toTopos.ringInverseImage.obj O)).mapIso
      (SheafOfModules.ChangeOfRings.extendRestrictUnitIso
        (Cocontinuous.structureMapIso
        (X := componentRingedSite C J O n) (Y := totalRingedSite C J O)
        (ofStage C n) (Iso.refl _))
        (((stageMorphism C J O n).toTopos.moduleInverseImage O).obj M))).symm ≪≫
    ((stageMorphism C J O n).toTopos.moduleInverseImageForgetIso O).app M ≪≫
    (Functor.CocontinuousPullback.comparisonIso (ofStage C n)
      (J n).toGrothendieck (topology C J)).app
      ((Sheaf.InternalModule.ToInternal.underlying O).obj M)

/-- The specified underlying comparisons are linear, natural, and mutually inverse. -/
private theorem moduleInverseImageIsoModulePullback_laws (n : SimplexCategory) :
    let R := componentRingSheaf C J O n
    let A := Cocontinuous.moduleInverseImage (J := (J n).toGrothendieck) (ofStage C n) O
    let B := (stageMorphism C J O n).modulePullback
    let α : ∀ M, (ToInternal.underlying R).obj (A.obj M) ⟶
        (ToInternal.underlying R).obj (B.obj M) := fun M ↦ (moduleInverseImage_underlyingIso C J O n M).hom ≫ (modulePullback_underlyingIso C J O n M).inv
    let β : ∀ M, (ToInternal.underlying R).obj (B.obj M) ⟶
        (ToInternal.underlying R).obj (A.obj M) := fun M ↦ (modulePullback_underlyingIso C J O n M).hom ≫ (moduleInverseImage_underlyingIso C J O n M).inv
    let Addα := ∀ M U (x y : (A.obj M).val.obj U),
      underlyingApp R (α M) U (x + y) =
        underlyingApp R (α M) U x + underlyingApp R (α M) U y
    let Smulα := ∀ M U (r : R.obj.obj U) (x : (A.obj M).val.obj U),
      underlyingApp R (α M) U (r • x) = r • underlyingApp R (α M) U x
    let Addβ := ∀ M U (x y : (B.obj M).val.obj U),
      underlyingApp R (β M) U (x + y) =
        underlyingApp R (β M) U x + underlyingApp R (β M) U y
    let Smulβ := ∀ M U (r : R.obj.obj U) (x : (B.obj M).val.obj U),
      underlyingApp R (β M) U (r • x) = r • underlyingApp R (β M) U x
    Addα ∧ Smulα ∧ Addβ ∧ Smulβ ∧
      ∀ (ha : Addα) (hs : Smulα) (hb : Addβ) (ht : Smulβ),
        let f := fun M ↦ homOfUnderlying R (α M) (ha M) (hs M)
        let g := fun M ↦ homOfUnderlying R (β M) (hb M) (ht M)
        (∀ M, f M ≫ g M = 𝟙 (A.obj M)) ∧
        (∀ M, g M ≫ f M = 𝟙 (B.obj M)) ∧
        (∀ {M N} (h : M ⟶ N), A.map h ≫ f N = f M ≫ B.map h) := by
  sorry

/-- Module inverse image along the component inclusion is canonically isomorphic to ringed-topos module pullback. -/
def moduleInverseImageIsoModulePullback (n : SimplexCategory) :
    Cocontinuous.moduleInverseImage (ofStage C n) O ≅ (stageMorphism C J O n).modulePullback := by
  let R := componentRingSheaf C J O n
  let A := Cocontinuous.moduleInverseImage (J := (J n).toGrothendieck) (ofStage C n) O
  let B := (stageMorphism C J O n).modulePullback
  let α : ∀ M, (ToInternal.underlying R).obj (A.obj M) ⟶
    (ToInternal.underlying R).obj (B.obj M) := fun M ↦ (moduleInverseImage_underlyingIso C J O n M).hom ≫ (modulePullback_underlyingIso C J O n M).inv
  let β : ∀ M, (ToInternal.underlying R).obj (B.obj M) ⟶
    (ToInternal.underlying R).obj (A.obj M) := fun M ↦ (modulePullback_underlyingIso C J O n M).hom ≫ (moduleInverseImage_underlyingIso C J O n M).inv
  have laws := moduleInverseImageIsoModulePullback_laws C J O n
  let f := fun M ↦ homOfUnderlying R (α M) (laws.1 M) (laws.2.1 M)
  let g := fun M ↦ homOfUnderlying R (β M) (laws.2.2.1 M) (laws.2.2.2.1 M)
  have h := laws.2.2.2.2 laws.1 laws.2.1 laws.2.2.1 laws.2.2.2.1
  exact NatIso.ofComponents
    (fun M ↦
      { hom := f M
        inv := g M
        hom_inv_id := h.1 M
        inv_hom_id := h.2.1 M })
    (fun hMN ↦ h.2.2 hMN)

/-- Continuous-site module pushforward along `u_φ` with the direct-image form of `O(φ)`. -/
abbrev ringedToposMap_pushforward {m n : SimplexCategory} (φ : m ⟶ n) :
    SheafOfModules.{w} (componentRingSheaf C J O n) ⥤
      SheafOfModules.{w} (componentRingSheaf C J O m) :=
  SheafOfModules.pushforward (ringedToposMapDirectStructure C J O φ)

/-- The identity component functions commute with presheaf restriction. -/
private theorem ringedToposMap_pushforward_underlyingIso_naturality {m n : SimplexCategory} (φ : m ⟶ n)
    (M : SheafOfModules.{w} (componentRingSheaf C J O n)) :
    let A := (sheafToPresheaf _ (Type w)).obj ((Sheaf.InternalModule.ToInternal.underlying (componentRingSheaf C J O m)).obj
      ((ringedToposMap_pushforward C J O φ).obj M))
    let B := (sheafToPresheaf _ (Type w)).obj (((C.map φ).toFunctor.sheafPushforwardContinuous (Type w)
        (J m).toGrothendieck (J n).toGrothendieck).obj
        ((Sheaf.InternalModule.ToInternal.underlying
          (componentRingSheaf C J O n)).obj M))
    ∀ {U V} (f : U ⟶ V),
      A.map f ≫ (Iso.refl (A.obj V)).hom =
        (Iso.refl (A.obj U)).hom ≫ B.map f := by
  sorry

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
    NatIso.ofComponents (fun _ ↦ Iso.refl _) (by
      intro U V f
      exact (ringedToposMap_pushforward_underlyingIso_naturality C J O φ M) f)

/-- The specified underlying comparisons are linear, natural, and mutually inverse. -/
private theorem ringedToposMap_pushforwardIso_laws {m n : SimplexCategory} (φ : m ⟶ n) :
    let R := componentRingSheaf C J O m
    let A := ringedToposMap_pushforward C J O φ
    let B := (ringedToposMap C J O φ).modulePushforward
    let α : ∀ M, (ToInternal.underlying R).obj (A.obj M) ⟶
        (ToInternal.underlying R).obj (B.obj M) := fun M ↦ (ringedToposMap_pushforward_underlyingIso C J O φ M).hom ≫
      (ToposHom.ModulePushforward.forgetIso (ringedToposMap C J O φ)).inv.app M
    let β : ∀ M, (ToInternal.underlying R).obj (B.obj M) ⟶
        (ToInternal.underlying R).obj (A.obj M) := fun M ↦ (ToposHom.ModulePushforward.forgetIso (ringedToposMap C J O φ)).hom.app M ≫
      (ringedToposMap_pushforward_underlyingIso C J O φ M).inv
    let Addα := ∀ M U (x y : (A.obj M).val.obj U),
      underlyingApp R (α M) U (x + y) =
        underlyingApp R (α M) U x + underlyingApp R (α M) U y
    let Smulα := ∀ M U (r : R.obj.obj U) (x : (A.obj M).val.obj U),
      underlyingApp R (α M) U (r • x) = r • underlyingApp R (α M) U x
    let Addβ := ∀ M U (x y : (B.obj M).val.obj U),
      underlyingApp R (β M) U (x + y) =
        underlyingApp R (β M) U x + underlyingApp R (β M) U y
    let Smulβ := ∀ M U (r : R.obj.obj U) (x : (B.obj M).val.obj U),
      underlyingApp R (β M) U (r • x) = r • underlyingApp R (β M) U x
    Addα ∧ Smulα ∧ Addβ ∧ Smulβ ∧
      ∀ (ha : Addα) (hs : Smulα) (hb : Addβ) (ht : Smulβ),
        let f := fun M ↦ homOfUnderlying R (α M) (ha M) (hs M)
        let g := fun M ↦ homOfUnderlying R (β M) (hb M) (ht M)
        (∀ M, f M ≫ g M = 𝟙 (A.obj M)) ∧
        (∀ M, g M ≫ f M = 𝟙 (B.obj M)) ∧
        (∀ {M N} (h : M ⟶ N), A.map h ≫ f N = f M ≫ B.map h) := by
  sorry

/-- Continuous-site module pushforward is canonically isomorphic to ringed-topos direct image. -/
def ringedToposMap_pushforwardIso {m n : SimplexCategory} (φ : m ⟶ n) :
    ringedToposMap_pushforward C J O φ ≅ (ringedToposMap C J O φ).modulePushforward := by
  let R := componentRingSheaf C J O m
  let A := ringedToposMap_pushforward C J O φ
  let B := (ringedToposMap C J O φ).modulePushforward
  let α : ∀ M, (ToInternal.underlying R).obj (A.obj M) ⟶
    (ToInternal.underlying R).obj (B.obj M) := fun M ↦ (ringedToposMap_pushforward_underlyingIso C J O φ M).hom ≫
    (ToposHom.ModulePushforward.forgetIso (ringedToposMap C J O φ)).inv.app M
  let β : ∀ M, (ToInternal.underlying R).obj (B.obj M) ⟶
    (ToInternal.underlying R).obj (A.obj M) := fun M ↦ (ToposHom.ModulePushforward.forgetIso (ringedToposMap C J O φ)).hom.app M ≫
    (ringedToposMap_pushforward_underlyingIso C J O φ M).inv
  have laws := ringedToposMap_pushforwardIso_laws C J O φ
  let f := fun M ↦ homOfUnderlying R (α M) (laws.1 M) (laws.2.1 M)
  let g := fun M ↦ homOfUnderlying R (β M) (laws.2.2.1 M) (laws.2.2.2.1 M)
  have h := laws.2.2.2.2 laws.1 laws.2.1 laws.2.2.1 laws.2.2.2.1
  exact NatIso.ofComponents
    (fun M ↦
      { hom := f M
        inv := g M
        hom_inv_id := h.1 M
        inv_hom_id := h.2.1 M })
    (fun hMN ↦ h.2.2 hMN)

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
private def moduleLowerShriek_componentAux {n m : SimplexCategory} (φ : n ⟶ m)
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
def moduleLowerShriek_componentCoproductHom (n m : SimplexCategory)
    [HasColimitsOfShape (Discrete (n ⟶ m))
      (SheafOfModules.{w} (componentRingSheaf C J O m))]
    (G : SheafOfModules.{w} (componentRingSheaf C J O n)) :
    (∐ fun φ : n ⟶ m ↦ (ringedToposMap C J O φ).modulePullback.obj G) ⟶
      (stageMorphism C J O m).modulePullback.obj ((moduleLowerShriek C J O n).obj G) :=
  Sigma.desc fun φ ↦ moduleLowerShriek_component C J O φ G

/-- The coproduct comparison is the coproduct of the component maps. -/
theorem moduleLowerShriek_componentCoproductHom_eq (n m : SimplexCategory)
    [HasColimitsOfShape (Discrete (n ⟶ m))
      (SheafOfModules.{w} (componentRingSheaf C J O m))]
    (G : SheafOfModules.{w} (componentRingSheaf C J O n)) :
    moduleLowerShriek_componentCoproductHom C J O n m G =
      Sigma.desc fun φ ↦ moduleLowerShriek_component C J O φ G :=
  rfl

/-- The coproduct comparison morphism is an isomorphism. -/
instance moduleLowerShriek_componentCoproductHom_isIso (n m : SimplexCategory)
    [HasColimitsOfShape (Discrete (n ⟶ m))
      (SheafOfModules.{w} (componentRingSheaf C J O m))]
    (G : SheafOfModules.{w} (componentRingSheaf C J O n)) :
    IsIso (moduleLowerShriek_componentCoproductHom C J O n m G) :=
  sorry


/-- The coproduct inclusion of `f_φ^* G` followed by the comparison is the component map. -/
theorem moduleLowerShriek_componentCoproduct_ι (n m : SimplexCategory)
    [HasColimitsOfShape (Discrete (n ⟶ m))
      (SheafOfModules.{w} (componentRingSheaf C J O m))]
    (G : SheafOfModules.{w} (componentRingSheaf C J O n)) (φ : n ⟶ m) :
    Sigma.ι (fun ψ : n ⟶ m ↦ (ringedToposMap C J O ψ).modulePullback.obj G) φ ≫
      moduleLowerShriek_componentCoproductHom C J O n m G =
      moduleLowerShriek_component C J O φ G :=
  Sigma.ι_desc (fun φ ↦ moduleLowerShriek_component C J O φ G) φ

/-- Pullback along the ringed component inclusion admits the canonical module lower shriek as left adjoint. -/
instance stageMorphism_modulePullback_isRightAdjoint (n : SimplexCategory) :
    ((stageMorphism C J O n).modulePullback).IsRightAdjoint :=
  (moduleLowerShriek.adjunction C J O n).ofNatIsoRight
    (moduleInverseImageIsoModulePullback C J O n) |>.isRightAdjoint

end CategoryTheory.SimplicialSites
