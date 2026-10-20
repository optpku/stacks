module

public import ReasLib.CategoryTheory.Sites.Simplicial.RingedMorphism
public import ReasLib.AlgebraicGeometry.RingedSite.Simplicial.LowerShriek
public import ReasLib.AlgebraicGeometry.RingedSite.Simplicial.Fiber
public import ReasLib.CategoryTheory.Sites.Topos.ModuleAdjunction

/-!
# Component morphisms of ringed simplicial sites

Total ringed morphisms induce component ringed morphisms, compatible inverse-image
squares, and natural comparisons between restriction and module direct image.
-/

-- The explicit constructions use private component maps and their proof laws.
set_option backward.privateInPublic true

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

namespace RingedMorphism

variable {J J' O O'}
variable (f : RingedMorphism J J' O O')
variable [∀ n (P : (C'.obj n)ᵒᵖ ⥤ Type w),
    ((f.toSimplicial.app n).toFunctor).op.HasLeftKanExtension P]
variable [∀ P : (totalSite C')ᵒᵖ ⥤ Type w,
    (IsMorphism.totalFunctor f.toSimplicial).op.HasLeftKanExtension P]
/-- The canonical ring-valued inverse images commute with restriction to each degree. -/
def inverseImage_comp (n : SimplexCategory) :
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

/-- The component ringed-topos morphism obtained by restricting the total structure map. -/
def topos (n : SimplexCategory) :
    ToposHom (componentRingedSite C J O n) (componentRingedSite C' J' O' n) where
  toTopos := IsMorphism.topos J J' f.toSimplicial n
  structureMap :=
    (IsMorphism.topos J J' f.toSimplicial n).ringInverseImage.map
        (Cocontinuous.structureMapIso
        (X := componentRingedSite C' J' O' n) (Y := totalRingedSite C' J' O')
        (ofStage C' n) (Iso.refl _)).inv ≫
      (inverseImage_comp f n).inv.app O' ≫
      (ofStageMorphism C J n).ringInverseImage.map f.structureMap ≫
      (Cocontinuous.structureMapIso
        (X := componentRingedSite C J O n) (Y := totalRingedSite C J O)
        (ofStage C n) (Iso.refl _)).hom

/-- The component ringed morphism has the given underlying component topos morphism. -/
theorem topos_toTopos (n : SimplexCategory) :
    (topos f n).toTopos = IsMorphism.topos J J' f.toSimplicial n :=
  rfl

/-- The component structure map is the restricted total structure map transported through the canonical ring comparisons. -/
theorem topos_structureMap (n : SimplexCategory) :
    (topos f n).structureMap =
      (IsMorphism.topos J J' f.toSimplicial n).ringInverseImage.map
          (Cocontinuous.structureMapIso
        (X := componentRingedSite C' J' O' n) (Y := totalRingedSite C' J' O')
        (ofStage C' n) (Iso.refl _)).inv ≫
        (inverseImage_comp f n).inv.app O' ≫
        (ofStageMorphism C J n).ringInverseImage.map f.structureMap ≫
        (Cocontinuous.structureMapIso
        (X := componentRingedSite C J O n) (Y := totalRingedSite C J O)
        (ofStage C n) (Iso.refl _)).hom :=
  rfl

/-- The inverse-image square respects the structure maps of the ring sheaves. -/
theorem inverseImage_comp_structureMap (n : SimplexCategory) :
    (ofStageMorphism C J n).ringInverseImage.map f.structureMap ≫
        (Cocontinuous.structureMapIso
        (X := componentRingedSite C J O n) (Y := totalRingedSite C J O)
        (ofStage C n) (Iso.refl _)).hom =
      (inverseImage_comp f n).hom.app O' ≫
        (IsMorphism.topos J J' f.toSimplicial n).ringInverseImage.map (Cocontinuous.structureMapIso
        (X := componentRingedSite C' J' O' n) (Y := totalRingedSite C' J' O')
        (ofStage C' n) (Iso.refl _)).hom ≫
        (topos f n).structureMap :=
  sorry

variable [UnivLE.{max u v, w}]
variable [∀ n, (SheafOfModules.restrictScalars.{w}
    (stageMorphism C J O n).structureMap).IsRightAdjoint]
variable [∀ n, (SheafOfModules.restrictScalars.{w}
    (stageMorphism C' J' O' n).structureMap).IsRightAdjoint]


/-- The canonical comparison of the underlying sheaves of the two mixed module functors. -/
private def restrict_modulePushforward_underlying (n : SimplexCategory)
    (M : SheafOfModules.{w} O) :
    (Sheaf.InternalModule.ToInternal.underlying (componentRingSheaf C' J' O' n)).obj
      (((toToposHom f).modulePushforward ⋙
        (stageMorphism C' J' O' n).modulePullback).obj M) ≅
      (Sheaf.InternalModule.ToInternal.underlying (componentRingSheaf C' J' O' n)).obj
        (((stageMorphism C J O n).modulePullback ⋙
          (topos f n).modulePushforward).obj M) :=
  CategoryTheory.SimplicialSites.modulePullback_underlyingIso C' J' O' n ((toToposHom f).modulePushforward.obj M) ≪≫
    (stageRestrict C' J' (Type w) n).mapIso
      ((ToposHom.ModulePushforward.forgetIso (toToposHom f)).app M) ≪≫
    (IsMorphism.restrict_pushforward_stageRestrict J J' f.toSimplicial n).app
      ((Sheaf.InternalModule.ToInternal.underlying O).obj M) ≪≫
    (IsMorphism.topos J J' f.toSimplicial n).pushforward.mapIso
      (CategoryTheory.SimplicialSites.modulePullback_underlyingIso C J O n M).symm ≪≫
    (ToposHom.ModulePushforward.forgetIso (topos f n)).symm.app
      ((stageMorphism C J O n).modulePullback.obj M)

/-- The specified underlying mixed comparison is natural in the module sheaf. -/
private theorem restrict_modulePushforward_underlying_naturality (n : SimplexCategory) :
    let A := (toToposHom f).modulePushforward ⋙ (stageMorphism C' J' O' n).modulePullback
    let B := (stageMorphism C J O n).modulePullback ⋙ (topos f n).modulePushforward
    let U := Sheaf.InternalModule.ToInternal.underlying (componentRingSheaf C' J' O' n)
    ∀ {M N : SheafOfModules.{w} O} (a : M ⟶ N),
      (A ⋙ U).map a ≫ (restrict_modulePushforward_underlying f n N).hom =
        (restrict_modulePushforward_underlying f n M).hom ≫ (B ⋙ U).map a :=
  sorry

/-- The forward mixed comparison preserves addition and the action of the component ring. -/
private theorem restrict_modulePushforward_linearity (n : SimplexCategory) :
    let A := (toToposHom f).modulePushforward ⋙ (stageMorphism C' J' O' n).modulePullback
    let R := componentRingSheaf C' J' O' n
    let α := fun M ↦ (restrict_modulePushforward_underlying f n M).hom
    (∀ M U (x y : (A.obj M).val.obj U),
      Sheaf.InternalModule.underlyingApp R (α M) U (x + y) =
        Sheaf.InternalModule.underlyingApp R (α M) U x +
          Sheaf.InternalModule.underlyingApp R (α M) U y) ∧
    (∀ M U (r : R.obj.obj U) (x : (A.obj M).val.obj U),
      Sheaf.InternalModule.underlyingApp R (α M) U (r • x) =
        r • Sheaf.InternalModule.underlyingApp R (α M) U x) :=
  sorry

/-- Restriction of module direct image to a degree is naturally isomorphic to component direct image of the restricted module. -/
def restrict_modulePushforward (n : SimplexCategory) :
    (toToposHom f).modulePushforward ⋙ (stageMorphism C' J' O' n).modulePullback ≅
      (stageMorphism C J O n).modulePullback ⋙ (topos f n).modulePushforward :=
  let e : ((toToposHom f).modulePushforward ⋙ (stageMorphism C' J' O' n).modulePullback) ⋙ Sheaf.InternalModule.ToInternal.underlying (componentRingSheaf C' J' O' n) ≅
      ((stageMorphism C J O n).modulePullback ⋙ (topos f n).modulePushforward) ⋙ Sheaf.InternalModule.ToInternal.underlying (componentRingSheaf C' J' O' n) :=
    NatIso.ofComponents (fun M ↦ restrict_modulePushforward_underlying f n M)
      (fun a ↦ restrict_modulePushforward_underlying_naturality f n a)
  Sheaf.InternalModule.functorIsoOfUnderlying (componentRingSheaf C' J' O' n) e
    (fun M U x y ↦ (restrict_modulePushforward_linearity f n).1 M U x y)
    (fun M U r x ↦ (restrict_modulePushforward_linearity f n).2 M U r x)

end RingedMorphism

end CategoryTheory.SimplicialSites

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

namespace RingedMorphism

variable {J J' O O'}
variable (f : RingedMorphism J J' O O')
variable [∀ n (P : (F.obj n)ᵒᵖ ⥤ Type w),
    ((f.toSimplicial.app n).toFunctor).op.HasPointwiseRightKanExtension P]
variable [∀ P : (Grothendieck F)ᵒᵖ ⥤ Type w,
    (Grothendieck.map f.toSimplicial).op.HasPointwiseRightKanExtension P]
variable [∀ n, ∀ P : (F.obj (op n))ᵒᵖ ⥤ Type w,
    ((f.toSimplicial.app (op n)).toFunctor ⋙ ι F' (op n)).op.HasPointwiseRightKanExtension P]
variable [∀ n, ∀ P : (F.obj (op n))ᵒᵖ ⥤ Type w,
    (ι F (op n) ⋙ Grothendieck.map f.toSimplicial).op.HasPointwiseRightKanExtension P]
/-- The canonical ring-valued inverse images commute with restriction to each degree. -/
def inverseImage_comp (n : SimplexCategory) :
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

/-- The component ringed-topos morphism obtained by restricting the total structure map. -/
def topos (n : SimplexCategory) :
    ToposHom (fiberComponentRingedSite F J O n) (fiberComponentRingedSite F' J' O' n) where
  toTopos := IsFiberwiseMorphism.topos J J' f.toSimplicial n
  structureMap :=
    (IsFiberwiseMorphism.topos J J' f.toSimplicial n).ringInverseImage.map
        (Cocontinuous.structureMapIso
        (X := fiberComponentRingedSite F' J' O' n) (Y := fiberTotalRingedSite F' J' O')
        (ι F' (op n)) (Iso.refl _)).inv ≫
      (inverseImage_comp f n).inv.app O' ≫
      (fiberMorphism F J n).ringInverseImage.map f.structureMap ≫
      (Cocontinuous.structureMapIso
        (X := fiberComponentRingedSite F J O n) (Y := fiberTotalRingedSite F J O)
        (ι F (op n)) (Iso.refl _)).hom

/-- The component ringed morphism has the given underlying component topos morphism. -/
theorem topos_toTopos (n : SimplexCategory) :
    (topos f n).toTopos = IsFiberwiseMorphism.topos J J' f.toSimplicial n :=
  rfl

/-- The component structure map is the restricted total structure map transported through the canonical ring comparisons. -/
theorem topos_structureMap (n : SimplexCategory) :
    (topos f n).structureMap =
      (IsFiberwiseMorphism.topos J J' f.toSimplicial n).ringInverseImage.map
          (Cocontinuous.structureMapIso
        (X := fiberComponentRingedSite F' J' O' n) (Y := fiberTotalRingedSite F' J' O')
        (ι F' (op n)) (Iso.refl _)).inv ≫
        (inverseImage_comp f n).inv.app O' ≫
        (fiberMorphism F J n).ringInverseImage.map f.structureMap ≫
        (Cocontinuous.structureMapIso
        (X := fiberComponentRingedSite F J O n) (Y := fiberTotalRingedSite F J O)
        (ι F (op n)) (Iso.refl _)).hom :=
  rfl

/-- The inverse-image square respects the structure maps of the ring sheaves. -/
theorem inverseImage_comp_structureMap (n : SimplexCategory) :
    (fiberMorphism F J n).ringInverseImage.map f.structureMap ≫
        (Cocontinuous.structureMapIso
        (X := fiberComponentRingedSite F J O n) (Y := fiberTotalRingedSite F J O)
        (ι F (op n)) (Iso.refl _)).hom =
      (inverseImage_comp f n).hom.app O' ≫
        (IsFiberwiseMorphism.topos J J' f.toSimplicial n).ringInverseImage.map (Cocontinuous.structureMapIso
        (X := fiberComponentRingedSite F' J' O' n) (Y := fiberTotalRingedSite F' J' O')
        (ι F' (op n)) (Iso.refl _)).hom ≫
        (topos f n).structureMap :=
  sorry

variable [UnivLE.{max u v, w}]
variable [∀ n, (SheafOfModules.restrictScalars.{w}
    (fiberStageMorphism F J O n).structureMap).IsRightAdjoint]
variable [∀ n, (SheafOfModules.restrictScalars.{w}
    (fiberStageMorphism F' J' O' n).structureMap).IsRightAdjoint]


/-- The mixed sheaf comparison transported to restriction along the fiber inclusions. -/
private def restrict_pushforward_fiberRestrict (n : SimplexCategory) :
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

/-- The canonical comparison of the underlying sheaves of the two mixed module functors. -/
private def restrict_modulePushforward_underlying (n : SimplexCategory)
    (M : SheafOfModules.{w} O) :
    (Sheaf.InternalModule.ToInternal.underlying (fiberComponentRingSheaf F' J' O' n)).obj
      (((toToposHom f).modulePushforward ⋙
        (fiberStageMorphism F' J' O' n).modulePullback).obj M) ≅
      (Sheaf.InternalModule.ToInternal.underlying (fiberComponentRingSheaf F' J' O' n)).obj
        (((fiberStageMorphism F J O n).modulePullback ⋙
          (topos f n).modulePushforward).obj M) :=
  CategoryTheory.Grothendieck.fiberModulePullback_underlyingIso F' J' O' n
      ((toToposHom f).modulePushforward.obj M) ≪≫
    (fiberRestrict F' J' (Type w) n).mapIso
      ((ToposHom.ModulePushforward.forgetIso (toToposHom f)).app M) ≪≫
    (restrict_pushforward_fiberRestrict f n).app
      ((Sheaf.InternalModule.ToInternal.underlying O).obj M) ≪≫
    (IsFiberwiseMorphism.topos J J' f.toSimplicial n).pushforward.mapIso
      (CategoryTheory.Grothendieck.fiberModulePullback_underlyingIso F J O n M).symm ≪≫
    (ToposHom.ModulePushforward.forgetIso (topos f n)).symm.app
      ((fiberStageMorphism F J O n).modulePullback.obj M)

/-- The specified underlying mixed comparison is natural in the module sheaf. -/
private theorem restrict_modulePushforward_underlying_naturality (n : SimplexCategory) :
    let A := (toToposHom f).modulePushforward ⋙ (fiberStageMorphism F' J' O' n).modulePullback
    let B := (fiberStageMorphism F J O n).modulePullback ⋙ (topos f n).modulePushforward
    let U := Sheaf.InternalModule.ToInternal.underlying (fiberComponentRingSheaf F' J' O' n)
    ∀ {M N : SheafOfModules.{w} O} (a : M ⟶ N),
      (A ⋙ U).map a ≫ (restrict_modulePushforward_underlying f n N).hom =
        (restrict_modulePushforward_underlying f n M).hom ≫ (B ⋙ U).map a :=
  sorry

/-- The forward mixed comparison preserves addition and the action of the component ring. -/
private theorem restrict_modulePushforward_linearity (n : SimplexCategory) :
    let A := (toToposHom f).modulePushforward ⋙ (fiberStageMorphism F' J' O' n).modulePullback
    let R := fiberComponentRingSheaf F' J' O' n
    let α := fun M ↦ (restrict_modulePushforward_underlying f n M).hom
    (∀ M U (x y : (A.obj M).val.obj U),
      Sheaf.InternalModule.underlyingApp R (α M) U (x + y) =
        Sheaf.InternalModule.underlyingApp R (α M) U x +
          Sheaf.InternalModule.underlyingApp R (α M) U y) ∧
    (∀ M U (r : R.obj.obj U) (x : (A.obj M).val.obj U),
      Sheaf.InternalModule.underlyingApp R (α M) U (r • x) =
        r • Sheaf.InternalModule.underlyingApp R (α M) U x) :=
  sorry

/-- Restriction of module direct image to a degree is naturally isomorphic to component direct image of the restricted module. -/
def restrict_modulePushforward (n : SimplexCategory) :
    (toToposHom f).modulePushforward ⋙ (fiberStageMorphism F' J' O' n).modulePullback ≅
      (fiberStageMorphism F J O n).modulePullback ⋙ (topos f n).modulePushforward :=
  let e : ((toToposHom f).modulePushforward ⋙ (fiberStageMorphism F' J' O' n).modulePullback) ⋙ Sheaf.InternalModule.ToInternal.underlying (fiberComponentRingSheaf F' J' O' n) ≅
      ((fiberStageMorphism F J O n).modulePullback ⋙ (topos f n).modulePushforward) ⋙ Sheaf.InternalModule.ToInternal.underlying (fiberComponentRingSheaf F' J' O' n) :=
    NatIso.ofComponents (fun M ↦ restrict_modulePushforward_underlying f n M)
      (fun a ↦ restrict_modulePushforward_underlying_naturality f n a)
  Sheaf.InternalModule.functorIsoOfUnderlying (fiberComponentRingSheaf F' J' O' n) e
    (fun M U x y ↦ (restrict_modulePushforward_linearity f n).1 M U x y)
    (fun M U r x ↦ (restrict_modulePushforward_linearity f n).2 M U r x)

end RingedMorphism

end CategoryTheory.Grothendieck
