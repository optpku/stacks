module

public import ReasLib.AlgebraicGeometry.RingedSite.Module.LowerShriek
public import ReasLib.AlgebraicGeometry.RingedSite.Topos.HomOfCocontinuous
public import ReasLib.AlgebraicGeometry.RingedSite.Topos.ModuleAdjunction
public import ReasLib.CategoryTheory.Sites.Grothendieck.LowerShriek
public import ReasLib.AlgebraicGeometry.RingedSite.Topos.Cocontinuous.StructureIso
public import ReasLib.Algebra.Category.ModuleCat.Sheaf.ChangeOfRings.Iso
public import ReasLib.Algebra.Category.ModuleCat.Sheaf.ChangeOfRings.Small

/-!
# Ringed fiber inclusions of a simplicial object of sites

The ringed topos morphisms `g_n` and `f_φ` along fiber
inclusions, module lower shriek, and the componentwise coproduct formula.
-/

-- Private laws and component maps remain implementation details of the explicit constructions.
set_option backward.privateInPublic true

@[expose] public section

open CategoryTheory CategoryTheory.Limits Opposite Functor
open RingedSite
open Sheaf.InternalModule

noncomputable section

universe u v w

namespace CategoryTheory.Grothendieck

variable (F : SimplicialObject Cat.{v, u}) (J : ∀ n, Precoverage (F.obj n))
variable [IsFiberwiseSite F J]
variable (O : Sheaf (topology F J) RingCat.{w})

/-- The total ringed site `(Sh(C_total), O)`. -/
abbrev fiberTotalRingedSite : RingedSite.{u, v, w} :=
  ofRingSheaf (topology F J) O

omit [IsFiberwiseSite F J] in
/-- The structure sheaf of `fiberTotalRingedSite F J O` is `O`. -/
theorem fiberTotalRingedSite_structureSheaf :
    (fiberTotalRingedSite F J O).structureSheaf = O :=
  rfl

/-- The ring sheaf `O_n` on the degree-`n` fiber, the continuous inverse image of `O`
along `ι F (op n)`. -/
abbrev fiberComponentRingSheaf (n : SimplexCategory) :
    Sheaf (J (op n)).toGrothendieck RingCat.{w} :=
  Cocontinuous.inverseImageRingSheaf (ι F (op n)) O

/-- `fiberComponentRingSheaf` is inverse image of `O` along `ι F (op n)`. -/
theorem fiberComponentRingSheaf_eq (n : SimplexCategory) :
    fiberComponentRingSheaf F J O n = Cocontinuous.inverseImageRingSheaf (ι F (op n)) O :=
  rfl

/-- The degree-`n` ringed site `(Sh(C_n), O_n)`. -/
abbrev fiberComponentRingedSite (n : SimplexCategory) : RingedSite.{u, v, w} :=
  ofRingSheaf (J (op n)).toGrothendieck (fiberComponentRingSheaf F J O n)

/-- The structure sheaf of `fiberComponentRingedSite F J O n` is `O_n`. -/
theorem fiberComponentRingedSite_structureSheaf (n : SimplexCategory) :
    (fiberComponentRingedSite F J O n).structureSheaf = fiberComponentRingSheaf F J O n :=
  rfl

variable [UnivLE.{max u v, w}]
variable [(topology F J).HasSheafCompose (CategoryTheory.forget RingCat.{w})]
variable [∀ n, ((J n).toGrothendieck).HasSheafCompose (CategoryTheory.forget RingCat.{w})]
variable [∀ n, HasSheafify (J n).toGrothendieck (Type w)]
variable [HasSheafify (topology F J) (Type w)]
variable [∀ n, ∀ P : (F.obj (op n))ᵒᵖ ⥤ Type w,
    (ι F (op n)).op.HasPointwiseRightKanExtension P]
variable [∀ (m n : SimplexCategory) (φ : m ⟶ n) (P : (F.obj (op n))ᵒᵖ ⥤ Type w),
    ((F.map φ.op).toFunctor).op.HasPointwiseRightKanExtension P]

/-- The identity comparison along `ι F (op n)` from which the structure map of `g_n` is
obtained, so `g_n⁻¹ O = O_n`. -/
def fiberStageIdentityComparison (n : SimplexCategory) :
    (ι F (op n)).op ⋙ (fiberTotalRingedSite F J O).structureSheaf.obj ⟶
      (fiberComponentRingedSite F J O n).structureSheaf.obj :=
  𝟙 ((ι F (op n)).op ⋙ O.obj)

omit [UnivLE.{max u v, w}] [(topology F J).HasSheafCompose (CategoryTheory.forget RingCat)] [∀ (n :
  SimplexCategoryᵒᵖ), (J n).toGrothendieck.HasSheafCompose (CategoryTheory.forget RingCat)] [∀ (n :
  SimplexCategoryᵒᵖ), HasSheafify (J n).toGrothendieck (Type w)] [HasSheafify (topology F J) (Type
  w)] [∀ (n : SimplexCategory) (P : (F.obj (op n) : Type u)ᵒᵖ ⥤ Type w), (ι F (op
  n)).op.HasPointwiseRightKanExtension P] [∀ (m n : SimplexCategory) (φ : m ⟶ n) (P : (F.obj (op
  n) : Type u)ᵒᵖ ⥤ Type w), (F.map φ.op).toFunctor.op.HasPointwiseRightKanExtension P] in
/-- `fiberStageIdentityComparison` is the identity on the restricted structure sheaf. -/
theorem fiberStageIdentityComparison_eq_id (n : SimplexCategory) :
    fiberStageIdentityComparison F J O n = 𝟙 ((ι F (op n)).op ⋙ O.obj) :=
  rfl

/-- The morphism of ringed topoi `g_n : (Sh(C_n), O_n) ⟶ (Sh(C_total), O)` induced by
the fiber inclusion `ι F (op n)`. -/
def fiberStageMorphism (n : SimplexCategory) :
    ToposHom (fiberComponentRingedSite F J O n) (fiberTotalRingedSite F J O) :=
  Cocontinuous.toRingedTopos (ι F (op n)) (fiberStageIdentityComparison F J O n)

omit [UnivLE.{max u v, w}] [HasSheafify (topology F J) (Type w)] [∀ (m n : SimplexCategory) (φ : m ⟶
  n) (P : (F.obj (op n) : Type u)ᵒᵖ ⥤ Type w), (F.map φ.op).toFunctor.op.HasPointwiseRightKanExtension P]
  in
/-- The underlying topos morphism of `fiberStageMorphism F J O n` is `fiberMorphism F J n`. -/
theorem fiberStageMorphism_toTopos (n : SimplexCategory) :
    (fiberStageMorphism F J O n).toTopos = fiberMorphism F J n :=
  rfl

/-- Presheaf form of `O(φ)` along a simplex operator. -/
def fiberRingedToposMapComparison {m n : SimplexCategory} (φ : m ⟶ n) :
    (F.map φ.op).toFunctor.op ⋙ (fiberComponentRingedSite F J O m).structureSheaf.obj ⟶
      (fiberComponentRingedSite F J O n).structureSheaf.obj :=
  whiskerRight (NatTrans.op (ιNatTrans φ.op)) O.obj

omit [UnivLE.{max u v, w}] [(topology F J).HasSheafCompose (CategoryTheory.forget RingCat)] [∀ (n :
  SimplexCategoryᵒᵖ), (J n).toGrothendieck.HasSheafCompose (CategoryTheory.forget RingCat)] [∀ (n :
  SimplexCategoryᵒᵖ), HasSheafify (J n).toGrothendieck (Type w)] [HasSheafify (topology F J) (Type
  w)] [∀ (n : SimplexCategory) (P : (F.obj (op n) : Type u)ᵒᵖ ⥤ Type w), (ι F (op
  n)).op.HasPointwiseRightKanExtension P] [∀ (m n : SimplexCategory) (φ : m ⟶ n) (P : (F.obj (op
  n) : Type u)ᵒᵖ ⥤ Type w), (F.map φ.op).toFunctor.op.HasPointwiseRightKanExtension P] in
/-- `fiberRingedToposMapComparison` is whiskering of `ιNatTrans` with `O`. -/
theorem fiberRingedToposMapComparison_eq {m n : SimplexCategory} (φ : m ⟶ n) :
    fiberRingedToposMapComparison F J O φ =
      whiskerRight (NatTrans.op (ιNatTrans φ.op)) O.obj :=
  rfl

/-- The morphism of ringed topoi `f_φ : (Sh(C_n), O_n) ⟶ (Sh(C_m), O_m)`, with
structure map `O(φ) : f_φ⁻¹ O_m ⟶ O_n`. -/
def fiberRingedToposMap {m n : SimplexCategory} (φ : m ⟶ n) :
    ToposHom (fiberComponentRingedSite F J O n) (fiberComponentRingedSite F J O m) :=
  Cocontinuous.toRingedTopos (F.map φ.op).toFunctor (fiberRingedToposMapComparison F J O φ)

omit [UnivLE.{max u v, w}] [(topology F J).HasSheafCompose (CategoryTheory.forget RingCat)]
  [HasSheafify (topology F J) (Type w)] [∀ (n : SimplexCategory) (P : (F.obj (op n) : Type u)ᵒᵖ ⥤ Type w),
  (ι F (op n)).op.HasPointwiseRightKanExtension P] in
/-- The underlying topos morphism of `fiberRingedToposMap F J O φ` is `toposMap F J φ`. -/
theorem fiberRingedToposMap_toTopos {m n : SimplexCategory} (φ : m ⟶ n) :
    (fiberRingedToposMap F J O φ).toTopos = toposMap F J φ :=
  rfl

/-- Module lower shriek `g_{n!}` along the degree-`n` fiber inclusion. -/
abbrev fiberModuleLowerShriek (n : SimplexCategory) :
    SheafOfModules.{w} (fiberComponentRingSheaf F J O n) ⥤ SheafOfModules.{w} O :=
  Cocontinuous.moduleLowerShriek (ι F (op n)) O

omit [UnivLE.{max u v, w}] [(topology F J).HasSheafCompose (CategoryTheory.forget RingCat)] [∀ (n :
  SimplexCategoryᵒᵖ), (J n).toGrothendieck.HasSheafCompose (CategoryTheory.forget RingCat)] [∀ (n :
  SimplexCategoryᵒᵖ), HasSheafify (J n).toGrothendieck (Type w)] [HasSheafify (topology F J) (Type
  w)] [∀ (n : SimplexCategory) (P : (F.obj (op n) : Type u)ᵒᵖ ⥤ Type w), (ι F (op
  n)).op.HasPointwiseRightKanExtension P] [∀ (m n : SimplexCategory) (φ : m ⟶ n) (P : (F.obj (op
  n) : Type u)ᵒᵖ ⥤ Type w), (F.map φ.op).toFunctor.op.HasPointwiseRightKanExtension P] in
/-- `fiberModuleLowerShriek` is the lower shriek along `ι F (op n)`. -/
theorem fiberModuleLowerShriek_eq (n : SimplexCategory) :
    fiberModuleLowerShriek F J O n = Cocontinuous.moduleLowerShriek (ι F (op n)) O :=
  rfl

/-- The canonical adjunction `g_{n!} ⊣` module inverse image along `ι F (op n)`. -/
def fiberModuleLowerShriek.adjunction (n : SimplexCategory) :
    fiberModuleLowerShriek F J O n ⊣ Cocontinuous.moduleInverseImage (ι F (op n)) O :=
  Cocontinuous.moduleLowerShriek.adjunction (ι F (op n)) O

omit [UnivLE.{max u v, w}] [(topology F J).HasSheafCompose (CategoryTheory.forget RingCat)] [∀ (n :
  SimplexCategoryᵒᵖ), (J n).toGrothendieck.HasSheafCompose (CategoryTheory.forget RingCat)] [∀ (n :
  SimplexCategoryᵒᵖ), HasSheafify (J n).toGrothendieck (Type w)] [HasSheafify (topology F J) (Type
  w)] [∀ (n : SimplexCategory) (P : (F.obj (op n) : Type u)ᵒᵖ ⥤ Type w), (ι F (op
  n)).op.HasPointwiseRightKanExtension P] [∀ (m n : SimplexCategory) (φ : m ⟶ n) (P : (F.obj (op
  n) : Type u)ᵒᵖ ⥤ Type w), (F.map φ.op).toFunctor.op.HasPointwiseRightKanExtension P] in
/-- The adjunction is the lower-shriek/inverse-image adjunction along `ι`. -/
theorem fiberModuleLowerShriek.adjunction_eq (n : SimplexCategory) :
    fiberModuleLowerShriek.adjunction F J O n =
      Cocontinuous.moduleLowerShriek.adjunction (ι F (op n)) O :=
  rfl

/-- The identity component functions commute with presheaf restriction. -/
private theorem fiberModuleInverseImage_underlyingIso_naturality (n : SimplexCategory)
    (M : SheafOfModules.{w} O) :
    let A := (sheafToPresheaf _ (Type w)).obj ((Sheaf.InternalModule.ToInternal.underlying (fiberComponentRingSheaf F J O n)).obj
      ((Cocontinuous.moduleInverseImage (ι F (op n)) O).obj M))
    let B := (sheafToPresheaf _ (Type w)).obj (((ι F (op n)).sheafPushforwardContinuous (Type w)
        (J (op n)).toGrothendieck (topology F J)).obj
        ((Sheaf.InternalModule.ToInternal.underlying O).obj M))
    ∀ {U V} (f : U ⟶ V),
      A.map f ≫ (Iso.refl (A.obj V)).hom =
        (Iso.refl (A.obj U)).hom ≫ B.map f := by
  sorry

/-- Underlying type-valued sheaf of module inverse image along `ι F (op n)`. -/
def fiberModuleInverseImage_underlyingIso (n : SimplexCategory)
    (M : SheafOfModules.{w} O) :
    (Sheaf.InternalModule.ToInternal.underlying (fiberComponentRingSheaf F J O n)).obj
      ((Cocontinuous.moduleInverseImage (ι F (op n)) O).obj M) ≅
      ((ι F (op n)).sheafPushforwardContinuous (Type w)
        (J (op n)).toGrothendieck (topology F J)).obj
        ((Sheaf.InternalModule.ToInternal.underlying O).obj M) :=
  (fullyFaithfulSheafToPresheaf ((J (op n)).toGrothendieck) (Type w)).preimageIso <|
    NatIso.ofComponents (fun _ ↦ Iso.refl _) (by
      intro U V f
      exact (fiberModuleInverseImage_underlyingIso_naturality F J O n M) f)

/-- The identity component functions commute with presheaf restriction. -/
private theorem fiberModulePullback_restrictScalars_underlyingIso_naturality (n : SimplexCategory)
    (M : SheafOfModules.{w} O) :
    let A := (sheafToPresheaf _ (Type w)).obj ((Sheaf.InternalModule.ToInternal.underlying (fiberComponentRingSheaf F J O n)).obj
      ((fiberStageMorphism F J O n).modulePullback.obj M))
    let B := (sheafToPresheaf _ (Type w)).obj ((Sheaf.InternalModule.ToInternal.underlying
          ((fiberStageMorphism F J O n).toTopos.ringInverseImage.obj O)).obj
        ((SheafOfModules.restrictScalars (fiberStageMorphism F J O n).structureMap).obj
          ((fiberStageMorphism F J O n).modulePullback.obj M)))
    ∀ {U V} (f : U ⟶ V),
      A.map f ≫ (Iso.refl (A.obj V)).hom =
        (Iso.refl (A.obj U)).hom ≫ B.map f := by
  sorry

/-- Restriction of scalars along the structure map of `g_n` does not change the
underlying type-valued sheaf of `g_n^* M`. -/
def fiberModulePullback_restrictScalars_underlyingIso (n : SimplexCategory)
    (M : SheafOfModules.{w} O) :
    (Sheaf.InternalModule.ToInternal.underlying (fiberComponentRingSheaf F J O n)).obj
      ((fiberStageMorphism F J O n).modulePullback.obj M) ≅
      (Sheaf.InternalModule.ToInternal.underlying
          ((fiberStageMorphism F J O n).toTopos.ringInverseImage.obj O)).obj
        ((SheafOfModules.restrictScalars (fiberStageMorphism F J O n).structureMap).obj
          ((fiberStageMorphism F J O n).modulePullback.obj M)) :=
  (fullyFaithfulSheafToPresheaf ((J (op n)).toGrothendieck) (Type w)).preimageIso <|
    NatIso.ofComponents (fun _ ↦ Iso.refl _) (by
      intro U V f
      exact (fiberModulePullback_restrictScalars_underlyingIso_naturality F J O n M) f)

/-- The scalar-extension unit comparing geometric inverse image with `g_n^*`. -/
def fiberModulePullback_scalarUnit (n : SimplexCategory)
    (M : SheafOfModules.{w} O) :
    ((fiberStageMorphism F J O n).toTopos.moduleInverseImage O).obj M ⟶
      (SheafOfModules.restrictScalars (fiberStageMorphism F J O n).structureMap).obj
        ((fiberStageMorphism F J O n).modulePullback.obj M) :=
  (SheafOfModules.ChangeOfRings.extendRestrictAdjunction
      (fiberStageMorphism F J O n).structureMap).unit.app
    (((fiberStageMorphism F J O n).toTopos.moduleInverseImage O).obj M)

/-- The scalar-extension unit is an isomorphism. -/
instance fiberModulePullback_scalarUnit_isIso (n : SimplexCategory)
    (M : SheafOfModules.{w} O) :
    IsIso (fiberModulePullback_scalarUnit F J O n M) :=
  (SheafOfModules.ChangeOfRings.extendRestrictUnitIso
    (Cocontinuous.structureMapIso
        (X := fiberComponentRingedSite F J O n) (Y := fiberTotalRingedSite F J O)
        (ι F (op n)) (Iso.refl _))
    (((fiberStageMorphism F J O n).toTopos.moduleInverseImage O).obj M)).isIso_hom


/-- Underlying type-valued sheaf of `g_n^*`. -/
def fiberModulePullback_underlyingIso (n : SimplexCategory)
    (M : SheafOfModules.{w} O) :
    (Sheaf.InternalModule.ToInternal.underlying (fiberComponentRingSheaf F J O n)).obj
      ((fiberStageMorphism F J O n).modulePullback.obj M) ≅
      ((ι F (op n)).sheafPushforwardContinuous (Type w)
        (J (op n)).toGrothendieck (topology F J)).obj
        ((Sheaf.InternalModule.ToInternal.underlying O).obj M) :=
  fiberModulePullback_restrictScalars_underlyingIso F J O n M ≪≫
    ((ToInternal.underlying
        ((fiberStageMorphism F J O n).toTopos.ringInverseImage.obj O)).mapIso
      (SheafOfModules.ChangeOfRings.extendRestrictUnitIso
        (Cocontinuous.structureMapIso
        (X := fiberComponentRingedSite F J O n) (Y := fiberTotalRingedSite F J O)
        (ι F (op n)) (Iso.refl _))
        (((fiberStageMorphism F J O n).toTopos.moduleInverseImage O).obj M))).symm ≪≫
    ((fiberStageMorphism F J O n).toTopos.moduleInverseImageForgetIso O).app M ≪≫
    (Functor.CocontinuousPullback.comparisonIso (ι F (op n))
      (J (op n)).toGrothendieck (topology F J)).app
      ((Sheaf.InternalModule.ToInternal.underlying O).obj M)

/-- The specified underlying comparisons are linear, natural, and mutually inverse. -/
private theorem fiberModuleInverseImageIsoModulePullback_laws (n : SimplexCategory) :
    let R := fiberComponentRingSheaf F J O n
    let A := Cocontinuous.moduleInverseImage (J := (J (op n)).toGrothendieck) (ι F (op n)) O
    let B := (fiberStageMorphism F J O n).modulePullback
    let α : ∀ M, (ToInternal.underlying R).obj (A.obj M) ⟶
        (ToInternal.underlying R).obj (B.obj M) := fun M ↦ (fiberModuleInverseImage_underlyingIso F J O n M).hom ≫ (fiberModulePullback_underlyingIso F J O n M).inv
    let β : ∀ M, (ToInternal.underlying R).obj (B.obj M) ⟶
        (ToInternal.underlying R).obj (A.obj M) := fun M ↦ (fiberModulePullback_underlyingIso F J O n M).hom ≫ (fiberModuleInverseImage_underlyingIso F J O n M).inv
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
def fiberModuleInverseImageIsoModulePullback (n : SimplexCategory) :
    Cocontinuous.moduleInverseImage (ι F (op n)) O ≅ (fiberStageMorphism F J O n).modulePullback := by
  let R := fiberComponentRingSheaf F J O n
  let A := Cocontinuous.moduleInverseImage (J := (J (op n)).toGrothendieck) (ι F (op n)) O
  let B := (fiberStageMorphism F J O n).modulePullback
  let α : ∀ M, (ToInternal.underlying R).obj (A.obj M) ⟶
    (ToInternal.underlying R).obj (B.obj M) := fun M ↦ (fiberModuleInverseImage_underlyingIso F J O n M).hom ≫ (fiberModulePullback_underlyingIso F J O n M).inv
  let β : ∀ M, (ToInternal.underlying R).obj (B.obj M) ⟶
    (ToInternal.underlying R).obj (A.obj M) := fun M ↦ (fiberModulePullback_underlyingIso F J O n M).hom ≫ (fiberModuleInverseImage_underlyingIso F J O n M).inv
  have laws := fiberModuleInverseImageIsoModulePullback_laws F J O n
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

/-- The identity component functions commute with presheaf restriction. -/
private theorem fiberRingedToposMap_restrictScalars_forgetIso_naturality {m n : SimplexCategory} (φ : m ⟶ n)
    (N : SheafOfModules.{w} (fiberComponentRingSheaf F J O n)) :
    let A := (sheafToPresheaf _ (Type w)).obj ((Sheaf.InternalModule.ToInternal.underlying
        ((fiberRingedToposMap F J O φ).toTopos.ringInverseImage.obj
          (fiberComponentRingSheaf F J O m))).obj
      ((SheafOfModules.restrictScalars (fiberRingedToposMap F J O φ).structureMap).obj N))
    let B := (sheafToPresheaf _ (Type w)).obj ((Sheaf.InternalModule.ToInternal.underlying (fiberComponentRingSheaf F J O n)).obj N)
    ∀ {U V} (f : U ⟶ V),
      A.map f ≫ (Iso.refl (A.obj V)).hom =
        (Iso.refl (A.obj U)).hom ≫ B.map f := by
  sorry

/-- Restriction of scalars along `O(φ)` does not change the underlying type-valued sheaf. -/
def fiberRingedToposMap_restrictScalars_forgetIso {m n : SimplexCategory} (φ : m ⟶ n)
    (N : SheafOfModules.{w} (fiberComponentRingSheaf F J O n)) :
    (Sheaf.InternalModule.ToInternal.underlying
        ((fiberRingedToposMap F J O φ).toTopos.ringInverseImage.obj
          (fiberComponentRingSheaf F J O m))).obj
      ((SheafOfModules.restrictScalars (fiberRingedToposMap F J O φ).structureMap).obj N) ≅
      (Sheaf.InternalModule.ToInternal.underlying (fiberComponentRingSheaf F J O n)).obj N :=
  (fullyFaithfulSheafToPresheaf ((J (op n)).toGrothendieck) (Type w)).preimageIso <|
    NatIso.ofComponents (fun _ ↦ Iso.refl _) (by
      intro U V f
      exact (fiberRingedToposMap_restrictScalars_forgetIso_naturality F J O φ N) f)

/-- The forward and reverse comparisons of `fiberRingedToposMap_restrictScalars_forgetIso`
are inverse. -/
theorem fiberRingedToposMap_restrictScalars_forgetIso_hom_inv_id {m n : SimplexCategory}
    (φ : m ⟶ n) (N : SheafOfModules.{w} (fiberComponentRingSheaf F J O n)) :
    (fiberRingedToposMap_restrictScalars_forgetIso F J O φ N).hom ≫
      (fiberRingedToposMap_restrictScalars_forgetIso F J O φ N).inv =
    𝟙 _ :=
  (fiberRingedToposMap_restrictScalars_forgetIso F J O φ N).hom_inv_id

/-- The `ιNatTrans` 2-cell on underlying type-valued sheaves. -/
private def fiberModuleLowerShriek_component_underlying {n m : SimplexCategory} (φ : n ⟶ m)
    (G : SheafOfModules.{w} (fiberComponentRingSheaf F J O n)) :
    ((F.map φ.op).toFunctor.sheafPullbackCocontinuous (Type w)
        (J (op m)).toGrothendieck (J (op n)).toGrothendieck).obj
      ((Sheaf.InternalModule.ToInternal.underlying
          (fiberComponentRingSheaf F J O n)).obj G) ⟶
      ((ι F (op m)).sheafPushforwardContinuous (Type w)
        (J (op m)).toGrothendieck (topology F J)).obj
        ((Sheaf.InternalModule.ToInternal.underlying O).obj
          ((fiberModuleLowerShriek F J O n).obj G)) :=
  (presheafToSheaf ((J (op m)).toGrothendieck) (Type w)).map
      (whiskerLeft (F.map φ.op).toFunctor.op
        ((sheafToPresheaf ((J (op n)).toGrothendieck) (Type w)).map
          ((Sheaf.InternalModule.ToInternal.underlying
              (fiberComponentRingSheaf F J O n)).map
            ((fiberModuleLowerShriek.adjunction F J O n).unit.app G) ≫
            (fiberModuleInverseImage_underlyingIso F J O n
              ((fiberModuleLowerShriek F J O n).obj G)).hom))) ≫
    (presheafToSheaf ((J (op m)).toGrothendieck) (Type w)).map
      (whiskerRight (NatTrans.op (ιNatTrans φ.op))
        ((Sheaf.InternalModule.ToInternal.underlying O).obj
          ((fiberModuleLowerShriek F J O n).obj G)).obj) ≫
    (sheafificationAdjunction ((J (op m)).toGrothendieck) (Type w)).counit.app
      (((ι F (op m)).sheafPushforwardContinuous (Type w)
          (J (op m)).toGrothendieck (topology F J)).obj
        ((Sheaf.InternalModule.ToInternal.underlying O).obj
          ((fiberModuleLowerShriek F J O n).obj G)))

/-- The geometric mate preserves addition and the scalar action of the inverse-image ring. -/
private theorem fiberModuleLowerShriek_component_geometric_laws {n m : SimplexCategory} (φ : n ⟶ m)
    (G : SheafOfModules.{w} (fiberComponentRingSheaf F J O n)) :
    let R := ((fiberRingedToposMap F J O φ).toTopos.ringInverseImage.obj
      (fiberComponentRingSheaf F J O n))
    let M := ((fiberRingedToposMap F J O φ).toTopos.moduleInverseImage
        (fiberComponentRingSheaf F J O n)).obj G
    let N := (SheafOfModules.restrictScalars (fiberRingedToposMap F J O φ).structureMap).obj
        ((Cocontinuous.moduleInverseImage (ι F (op m)) O).obj
          ((fiberModuleLowerShriek F J O n).obj G))
    let α : (ToInternal.underlying R).obj M ⟶ (ToInternal.underlying R).obj N := (((fiberRingedToposMap F J O φ).toTopos.moduleInverseImageForgetIso
        (fiberComponentRingSheaf F J O n)).hom.app G ≫
      fiberModuleLowerShriek_component_underlying F J O φ G ≫
      (fiberModuleInverseImage_underlyingIso F J O m
        ((fiberModuleLowerShriek F J O n).obj G)).inv ≫
      (fiberRingedToposMap_restrictScalars_forgetIso F J O φ
        ((Cocontinuous.moduleInverseImage (ι F (op m)) O).obj
          ((fiberModuleLowerShriek F J O n).obj G))).inv)
    (∀ U (x y : M.val.obj U), underlyingApp R α U (x + y) =
      underlyingApp R α U x + underlyingApp R α U y) ∧
    (∀ U (r : R.obj.obj U) (x : M.val.obj U),
      underlyingApp R α U (r • x) = r • underlyingApp R α U x) := by
  sorry

/-- Geometric inverse-image form of the component map, before extending scalars along `O(φ)`. -/
private def fiberModuleLowerShriek_component_geometric {n m : SimplexCategory} (φ : n ⟶ m)
    (G : SheafOfModules.{w} (fiberComponentRingSheaf F J O n)) :
    ((fiberRingedToposMap F J O φ).toTopos.moduleInverseImage
        (fiberComponentRingSheaf F J O n)).obj G ⟶
      (SheafOfModules.restrictScalars (fiberRingedToposMap F J O φ).structureMap).obj
        ((Cocontinuous.moduleInverseImage (ι F (op m)) O).obj
          ((fiberModuleLowerShriek F J O n).obj G)) :=
  Sheaf.InternalModule.homOfUnderlying
    ((fiberRingedToposMap F J O φ).toTopos.ringInverseImage.obj
      (fiberComponentRingSheaf F J O n))
    (((fiberRingedToposMap F J O φ).toTopos.moduleInverseImageForgetIso
        (fiberComponentRingSheaf F J O n)).hom.app G ≫
      fiberModuleLowerShriek_component_underlying F J O φ G ≫
      (fiberModuleInverseImage_underlyingIso F J O m
        ((fiberModuleLowerShriek F J O n).obj G)).inv ≫
      (fiberRingedToposMap_restrictScalars_forgetIso F J O φ
        ((Cocontinuous.moduleInverseImage (ι F (op m)) O).obj
          ((fiberModuleLowerShriek F J O n).obj G))).inv)
    (fiberModuleLowerShriek_component_geometric_laws F J O φ G).1
    (fiberModuleLowerShriek_component_geometric_laws F J O φ G).2

/-- The canonical component map `f_φ^* G ⟶ (g_{n!} G)_m`, using the lower-shriek
unit and the mate of `ιNatTrans`, then extending scalars along `O(φ)`. -/
def fiberModuleLowerShriek_component {n m : SimplexCategory} (φ : n ⟶ m)
    (G : SheafOfModules.{w} (fiberComponentRingSheaf F J O n)) :
    (fiberRingedToposMap F J O φ).modulePullback.obj G ⟶
      (fiberStageMorphism F J O m).modulePullback.obj
        ((fiberModuleLowerShriek F J O n).obj G) :=
  (ToposHom.ModulePullback.scalarHomEquiv (fiberRingedToposMap F J O φ)
      (((fiberRingedToposMap F J O φ).toTopos.moduleInverseImage
          (fiberComponentRingSheaf F J O n)).obj G)
      ((fiberStageMorphism F J O m).modulePullback.obj
        ((fiberModuleLowerShriek F J O n).obj G))).symm
    (fiberModuleLowerShriek_component_geometric F J O φ G ≫
      (SheafOfModules.restrictScalars (fiberRingedToposMap F J O φ).structureMap).map
        ((fiberModuleInverseImageIsoModulePullback F J O m).hom.app
          ((fiberModuleLowerShriek F J O n).obj G)))

/-- The component map is the scalar-extension adjunct of the geometric `ιNatTrans` mate,
transported along `fiberModuleInverseImageIsoModulePullback`. -/
theorem fiberModuleLowerShriek_component_adjunct {n m : SimplexCategory} (φ : n ⟶ m)
    (G : SheafOfModules.{w} (fiberComponentRingSheaf F J O n)) :
    (ToposHom.ModulePullback.scalarHomEquiv (fiberRingedToposMap F J O φ)
        (((fiberRingedToposMap F J O φ).toTopos.moduleInverseImage
            (fiberComponentRingSheaf F J O n)).obj G)
        ((fiberStageMorphism F J O m).modulePullback.obj
          ((fiberModuleLowerShriek F J O n).obj G)))
      (fiberModuleLowerShriek_component F J O φ G) =
      fiberModuleLowerShriek_component_geometric F J O φ G ≫
        (SheafOfModules.restrictScalars (fiberRingedToposMap F J O φ).structureMap).map
          ((fiberModuleInverseImageIsoModulePullback F J O m).hom.app
            ((fiberModuleLowerShriek F J O n).obj G)) :=
  by
  exact Equiv.apply_symm_apply _ _

/-- The coproduct comparison morphism. -/
def fiberModuleLowerShriek_componentCoproductHom (n m : SimplexCategory)
    [HasColimitsOfShape (Discrete (n ⟶ m))
      (SheafOfModules.{w} (fiberComponentRingSheaf F J O m))]
    (G : SheafOfModules.{w} (fiberComponentRingSheaf F J O n)) :
    (∐ fun φ : n ⟶ m ↦ (fiberRingedToposMap F J O φ).modulePullback.obj G) ⟶
      (fiberStageMorphism F J O m).modulePullback.obj
        ((fiberModuleLowerShriek F J O n).obj G) :=
  Sigma.desc fun φ ↦ fiberModuleLowerShriek_component F J O φ G

/-- The fiberwise coproduct comparison is the coproduct of the component maps. -/
theorem fiberModuleLowerShriek_componentCoproductHom_eq (n m : SimplexCategory)
    [HasColimitsOfShape (Discrete (n ⟶ m))
      (SheafOfModules.{w} (fiberComponentRingSheaf F J O m))]
    (G : SheafOfModules.{w} (fiberComponentRingSheaf F J O n)) :
    fiberModuleLowerShriek_componentCoproductHom F J O n m G =
      Sigma.desc fun φ ↦ fiberModuleLowerShriek_component F J O φ G :=
  rfl

/-- The fiberwise coproduct comparison morphism is an isomorphism. -/
instance fiberModuleLowerShriek_componentCoproductHom_isIso (n m : SimplexCategory)
    [HasColimitsOfShape (Discrete (n ⟶ m))
      (SheafOfModules.{w} (fiberComponentRingSheaf F J O m))]
    (G : SheafOfModules.{w} (fiberComponentRingSheaf F J O n)) :
    IsIso (fiberModuleLowerShriek_componentCoproductHom F J O n m G) :=
  sorry


/-- The coproduct inclusion of `f_φ^* G` followed by the comparison is the component map. -/
theorem fiberModuleLowerShriek_componentCoproduct_ι (n m : SimplexCategory)
    [HasColimitsOfShape (Discrete (n ⟶ m))
      (SheafOfModules.{w} (fiberComponentRingSheaf F J O m))]
    (G : SheafOfModules.{w} (fiberComponentRingSheaf F J O n)) (φ : n ⟶ m) :
    Sigma.ι (fun ψ : n ⟶ m ↦
        (fiberRingedToposMap F J O ψ).modulePullback.obj G) φ ≫
      fiberModuleLowerShriek_componentCoproductHom F J O n m G =
      fiberModuleLowerShriek_component F J O φ G :=
  Sigma.ι_desc (fun φ ↦ fiberModuleLowerShriek_component F J O φ G) φ

/-- Pullback along the ringed fiber inclusion admits the canonical module lower shriek as left adjoint. -/
instance fiberStageMorphism_modulePullback_isRightAdjoint (n : SimplexCategory) :
    ((fiberStageMorphism F J O n).modulePullback).IsRightAdjoint :=
  (fiberModuleLowerShriek.adjunction F J O n).ofNatIsoRight
    (fiberModuleInverseImageIsoModulePullback F J O n) |>.isRightAdjoint

end CategoryTheory.Grothendieck
