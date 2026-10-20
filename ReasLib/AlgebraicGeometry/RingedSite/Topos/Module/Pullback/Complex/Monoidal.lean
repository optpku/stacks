module

public import Mathlib.Algebra.Homology.Additive
public import Mathlib.CategoryTheory.Sites.CartesianMonoidal
public import ReasLib.Algebra.Category.ModuleCat.Presheaf.Tensor.Bilinear
public import ReasLib.Algebra.Category.ModuleCat.Sheaf.RingedSiteTensorUnit
public import ReasLib.Algebra.Homology.CochainComplex.Monoidal.Functor
public import ReasLib.Algebra.Category.ModuleCat.Sheaf.RingedSite.Complex.Monoidal
public import ReasLib.AlgebraicGeometry.RingedSite.Topos.Module.Pullback.Complex
public import ReasLib.AlgebraicGeometry.RingedSite.Topos.ModuleAdjunction
public import ReasLib.CategoryTheory.Adjunction.HomotopyCategory
public import ReasLib.CategoryTheory.Adjunction.LeftExact
import Mathlib.Tactic.CrossRefAttribute

/-!
# Complex pushforward and monoidal glue along morphisms of ringed topoi

Module pushforward along `RingedSite.ToposHom` acts degreewise on unbounded cochain complexes.
On commutative presentations the module adjunction is upgraded to a monoidal adjunction of
complexes, so differential graded algebras can be transported by `DGA.map`.
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits CategoryTheory.MonoidalCategory
open CategoryTheory.CartesianMonoidalCategory ComplexShape
open CategoryTheory.Functor.LaxMonoidal CategoryTheory.Functor.OplaxMonoidal
open CategoryTheory.Sheaf.InternalModule
open SheafOfModules.RingedSite
open scoped TensorProduct

noncomputable section

universe uX vX uY vY w uC vC

namespace RingedSite.ToposHom

variable {X : RingedSite.{uX, vX, w}} {Y : RingedSite.{uY, vY, w}}
variable [X.siteTopology.HasSheafCompose (forget RingCat.{w})]
  [Y.siteTopology.HasSheafCompose (forget RingCat.{w})]

/-- Module pushforward along an arbitrary morphism of ringed topoi, applied degreewise to
unbounded cochain complexes. -/
noncomputable def modulePushforwardComplex (f : ToposHom X Y) :
    CochainComplex (SheafOfModules.{w} X.structureSheaf) ℤ ⥤
      CochainComplex (SheafOfModules.{w} Y.structureSheaf) ℤ :=
  @Functor.mapHomologicalComplex _ _ _ _ _ _ _ f.modulePushforward
    (@Functor.preservesZeroMorphisms_of_additive _ _ _ _ _ _ f.modulePushforward
      (modulePushforward_additive f)) (up ℤ)

namespace modulePushforwardComplex

/-- In every degree, ringed-topos complex pushforward is the underlying module pushforward. -/
@[simp]
theorem obj_X (f : ToposHom X Y)
    (K : CochainComplex (SheafOfModules.{w} X.structureSheaf) ℤ) (n : ℤ) :
    ((f.modulePushforwardComplex).obj K).X n = f.modulePushforward.obj (K.X n) := sorry

end modulePushforwardComplex

/-- The degreewise pullback of complexes is left adjoint to degreewise pushforward. -/
noncomputable def modulePullbackPushforwardComplexAdjunction
    (f : ToposHom X Y)
    [(SheafOfModules.restrictScalars.{w} f.structureMap).IsRightAdjoint] :
    f.modulePullbackComplex ⊣ f.modulePushforwardComplex :=
  @Adjunction.mapHomologicalComplexAdjunction _ _ _ _ _ _ _ _
    (modulePullback_additive f) (modulePushforward_additive f) f.moduleAdjunction (up ℤ)

section CommRing

variable {CX : Type uX} [Category.{vX} CX]
variable {CY : Type uY} [Category.{vY} CY]
variable {JX : GrothendieckTopology CX} {JY : GrothendieckTopology CY}
variable [JX.HasSheafCompose (forget₂ CommRingCat.{w} RingCat.{w})]
variable [JY.HasSheafCompose (forget₂ CommRingCat.{w} RingCat.{w})]
variable [JX.HasSheafCompose (forget RingCat.{w})]
variable [JY.HasSheafCompose (forget RingCat.{w})]
variable [HasWeakSheafify JX AddCommGrpCat.{w}]
variable [JX.WEqualsLocallyBijective AddCommGrpCat.{w}]
variable [HasWeakSheafify JY AddCommGrpCat.{w}]
variable [JY.WEqualsLocallyBijective AddCommGrpCat.{w}]
variable [UnivLE.{max uX vX, w}] [UnivLE.{max uY vY, w}]
variable {OX : Sheaf JX CommRingCat.{w}} {OY : Sheaf JY CommRingCat.{w}}
variable (f : ToposHom (ofCommRingSheaf JX OX) (ofCommRingSheaf JY OY))
variable [(SheafOfModules.restrictScalars.{w} f.structureMap).IsRightAdjoint]

/-- The sheaf tensor of modules is sheafification of the pointwise tensor of underlying module
presheaves. -/
noncomputable def moduleTensorSheafifyIso
    {C : Type uC} [Category.{vC} C] {J : GrothendieckTopology C}
    [J.HasSheafCompose (forget₂ CommRingCat.{w} RingCat.{w})]
    [HasWeakSheafify J AddCommGrpCat.{w}]
    [J.WEqualsLocallyBijective AddCommGrpCat.{w}]
    (O : Sheaf J CommRingCat.{w})
    (F G : ringedSiteModuleCategory J O) :
    moduleTensor F G ≅ (moduleSheafification O).obj (F.val ⊗ G.val) :=
  tensorIso (moduleSheafificationValIso O F).symm
      (moduleSheafificationValIso O G).symm ≪≫
    Functor.Monoidal.μIso (moduleSheafification O) F.val G.val

/-- The type-valued sheaf morphism sending a pair of local sections to their pure tensor. -/
noncomputable def tensorSectionUnderlying
    {C : Type uC} [Category.{vC} C] {J : GrothendieckTopology C}
    [J.HasSheafCompose (forget₂ CommRingCat.{w} RingCat.{w})]
    [J.HasSheafCompose (forget RingCat.{w})]
    [HasWeakSheafify J AddCommGrpCat.{w}]
    [J.WEqualsLocallyBijective AddCommGrpCat.{w}]
    (O : Sheaf J CommRingCat.{w})
    (M N : ringedSiteModuleCategory J O) :
    (ToInternal.underlying (ofCommRingSheaf J O).structureSheaf).obj M ⊗
      (ToInternal.underlying (ofCommRingSheaf J O).structureSheaf).obj N ⟶
      (ToInternal.underlying (ofCommRingSheaf J O).structureSheaf).obj (moduleTensor M N) :=
  let UF := (ToInternal.underlying (ofCommRingSheaf J O).structureSheaf).obj M
  let UG := (ToInternal.underlying (ofCommRingSheaf J O).structureSheaf).obj N
  { hom :=
      { app := fun U ↦
          TypeCat.ofHom fun p ↦
            ((moduleTensorSheafifyIso O M N).inv.val.app U).hom
              (((moduleSheafificationUnitToVal O (M.val ⊗ N.val)).app U).hom
                ((fst UF UG).hom.app U p ⊗ₜ (snd UF UG).hom.app U p))
        naturality := fun {_ _} _ ↦ sorry } }

/-- The canonical lax comparison `f_* P × f_* Q ⟶ f_*(P × Q)` of type-valued direct image. -/
noncomputable def typePushforward_prodLax
    (P Q : Sheaf JX (Type w)) :
    f.toTopos.pushforward.obj P ⊗ f.toTopos.pushforward.obj Q ⟶
      f.toTopos.pushforward.obj (P ⊗ Q) :=
  f.toTopos.adjunction.homEquiv _ _
    (prodComparison f.toTopos.inverseImage
        (f.toTopos.pushforward.obj P) (f.toTopos.pushforward.obj Q) ≫
      (f.toTopos.adjunction.counit.app P ⊗ₘ f.toTopos.adjunction.counit.app Q))

/-- The cartesian type-valued comparison `f_* M × f_* N ⟶ f_*(M ⊗ N)` transported along
`ModulePushforward.forgetIso`. -/
noncomputable def modulePushforwardTensorUnderlying
    (M N : ringedSiteModuleCategory JX OX) :
    (ToInternal.underlying (ofCommRingSheaf JY OY).structureSheaf).obj
        (f.modulePushforward.obj M) ⊗
      (ToInternal.underlying (ofCommRingSheaf JY OY).structureSheaf).obj
        (f.modulePushforward.obj N) ⟶
      (ToInternal.underlying (ofCommRingSheaf JY OY).structureSheaf).obj
        (f.modulePushforward.obj (moduleTensor M N)) :=
  ((ModulePushforward.forgetIso f).hom.app M ⊗ₘ
      (ModulePushforward.forgetIso f).hom.app N) ≫
    typePushforward_prodLax f
        ((ToInternal.underlying (ofCommRingSheaf JX OX).structureSheaf).obj M)
        ((ToInternal.underlying (ofCommRingSheaf JX OX).structureSheaf).obj N) ≫
      f.toTopos.pushforward.map (tensorSectionUnderlying OX M N) ≫
        (ModulePushforward.forgetIso f).inv.app (moduleTensor M N)

/-- The compatible bilinear map representing the pushforward tensorator on underlying
module presheaves. -/
noncomputable def modulePushforwardTensorBilinear
    (M N : ringedSiteModuleCategory JX OX) :
    PresheafOfModules.BilinearMap OY.obj
      (f.modulePushforward.obj M).val
      (f.modulePushforward.obj N).val
      (f.modulePushforward.obj (moduleTensor M N)).val where
  app U :=
    { toFun := fun x ↦
        { toFun := fun y ↦
            (modulePushforwardTensorUnderlying f M N).hom.app U (x, y)
          map_add' := fun _ _ ↦ sorry
          map_smul' := fun _ _ ↦ sorry }
      map_add' := fun _ _ ↦ sorry
      map_smul' := fun _ _ ↦ sorry }
  naturality {_ _} _ _ _ := sorry

/-- The lax tensor comparison `f_* M ⊗ f_* N ⟶ f_*(M ⊗ N)` for module pushforward. -/
noncomputable def modulePushforward_μ
    (M N : ringedSiteModuleCategory JX OX) :
    moduleTensor (f.modulePushforward.obj M) (f.modulePushforward.obj N) ⟶
      f.modulePushforward.obj (moduleTensor M N) :=
  (moduleTensorSheafifyIso OY (f.modulePushforward.obj M) (f.modulePushforward.obj N)).hom ≫
    (moduleSheafification OY).map
      (PresheafOfModules.BilinearMap.toHom (modulePushforwardTensorBilinear f M N)) ≫
    (moduleSheafificationValIso OY (f.modulePushforward.obj (moduleTensor M N))).hom

/-- The underlying type-valued sheaf of a structure module agrees on sections with the
underlying structure sheaf. -/
noncomputable def unitModuleUnderlyingIso
    {C : Type uC} [Category.{vC} C] {J : GrothendieckTopology C}
    [J.HasSheafCompose (forget₂ CommRingCat.{w} RingCat.{w})]
    [J.HasSheafCompose (forget RingCat.{w})]
    (O : Sheaf J CommRingCat.{w}) :
    (ToInternal.underlying (CategoryTheory.Sheaf.ringSheafOfComm O)).obj (unitModule J O) ≅
      Hom.underlyingStructureSheaf (ofCommRingSheaf J O) where
  hom := { hom := { app := fun _ ↦ TypeCat.ofHom fun t ↦ t, naturality := fun {_ _} _ ↦ sorry } }
  inv := { hom := { app := fun _ ↦ TypeCat.ofHom fun t ↦ t, naturality := fun {_ _} _ ↦ sorry } }
  hom_inv_id := sorry
  inv_hom_id := sorry

/-- The type-valued unit comparison for module pushforward, obtained from the direct-image
structure map. -/
noncomputable def modulePushforward_unitUnderlying :
    (ToInternal.underlying (ofCommRingSheaf JY OY).structureSheaf).obj (unitModule JY OY) ⟶
      (ToInternal.underlying (ofCommRingSheaf JY OY).structureSheaf).obj
        (f.modulePushforward.obj (unitModule JX OX)) :=
  (unitModuleUnderlyingIso OY).hom ≫
    f.underlyingDirectImageMap ≫
      f.toTopos.pushforward.map (unitModuleUnderlyingIso OX).inv ≫
        (ModulePushforward.forgetIso f).inv.app (unitModule JX OX)

/-- The module-level unit comparison `O_Y ⟶ f_* O_X`. -/
noncomputable def modulePushforward_unitComparison :
    unitModule JY OY ⟶ f.modulePushforward.obj (unitModule JX OX) :=
  homOfUnderlying
    (ofCommRingSheaf JY OY).structureSheaf
    (modulePushforward_unitUnderlying f) sorry sorry

/-- The lax unit comparison on tensor units, via the structure-module identifications. -/
noncomputable def modulePushforward_ε :
    𝟙_ (ringedSiteModuleCategory JY OY) ⟶
      f.modulePushforward.obj (𝟙_ (ringedSiteModuleCategory JX OX)) :=
  unitIsoTensorUnit.inv ≫
    modulePushforward_unitComparison f ≫
      f.modulePushforward.map unitIsoTensorUnit.hom

/-- Module pushforward along a morphism of ringed topoi is canonically lax monoidal. -/
@[implicit_reducible]
noncomputable def modulePushforward.laxMonoidal : f.modulePushforward.LaxMonoidal where
  ε := modulePushforward_ε f
  μ := modulePushforward_μ f
  μ_natural_left {_ _} _ _ := sorry
  μ_natural_right {_ _} _ _ := sorry
  associativity _ _ _ := sorry
  left_unitality _ := sorry
  right_unitality _ := sorry

/-- Module pullback is oplax monoidal as the left adjoint of lax monoidal pushforward. -/
@[implicit_reducible]
noncomputable def modulePullback.oplaxMonoidal : f.modulePullback.OplaxMonoidal where
  η := (f.moduleAdjunction.homEquiv _ _).symm (ε f.modulePushforward (self := modulePushforward.laxMonoidal f))
  δ X Y := (f.moduleAdjunction.homEquiv _ _).symm
    ((f.moduleAdjunction.unit.app X ⊗ₘ f.moduleAdjunction.unit.app Y) ≫
      μ f.modulePushforward (self := modulePushforward.laxMonoidal f)
        (f.modulePullback.obj X) (f.modulePullback.obj Y))
  δ_natural_left {_ _} _ _ := sorry
  δ_natural_right {_ _} _ _ := sorry
  oplax_associativity _ _ _ := sorry
  oplax_left_unitality _ := sorry
  oplax_right_unitality _ := sorry

/-- The unit comparison for module pullback is invertible. -/
theorem modulePullback_η_isIso : IsIso (η f.modulePullback (self := modulePullback.oplaxMonoidal f)) := sorry

/-- The tensor comparison for module pullback is invertible. -/
theorem modulePullback_δ_isIso
    (M N : ringedSiteModuleCategory JY OY) :
    IsIso (δ f.modulePullback (self := modulePullback.oplaxMonoidal f) M N) := sorry

/-- The strong-monoidal core of module pullback, obtained from invertibility of the oplax
comparisons. -/
noncomputable def modulePullback.coreMonoidal : f.modulePullback.CoreMonoidal where
  εIso := (@asIso _ _ _ _
    (η f.modulePullback (self := modulePullback.oplaxMonoidal f))
    (modulePullback_η_isIso f)).symm
  μIso X Y := (@asIso _ _ _ _
    (δ f.modulePullback (self := modulePullback.oplaxMonoidal f) X Y)
    (modulePullback_δ_isIso f X Y)).symm
  μIso_hom_natural_left {_ _} _ _ := sorry
  μIso_hom_natural_right {_ _} _ _ := sorry
  associativity _ _ _ := sorry
  left_unitality _ := sorry
  right_unitality _ := sorry

/-- Module pullback along a morphism of ringed topoi is canonically strong monoidal. -/
@[implicit_reducible]
noncomputable def modulePullback.monoidal : f.modulePullback.Monoidal :=
  (modulePullback.coreMonoidal f).toMonoidal

/-- Termwise images of pointwise tensor bicomplexes along module pullback admit unbounded
totalization. -/
theorem modulePullback.hasMappedTensorTotals :
    @Functor.Cochain.HasMappedTensorTotals _ _ _ _ _ _ _ _ f.modulePullback
      (modulePullback_additive f) := sorry

/-- The tensor comparison for degreewise module pullback is invertible because module pullback,
as a left adjoint, preserves the coproducts used by totalization. -/
theorem modulePullbackComplex.tensorComparisonIsIso
    (K L : CochainComplex (ringedSiteModuleCategory JY OY) ℤ) :
    IsIso (@Functor.Cochain.tensorComparison _ _ _ _ _ _ _ _ _ _ _ _
      f.modulePullback (modulePullback_additive f) (modulePullback.monoidal f)
      K L _ _ (modulePullback.hasMappedTensorTotals f K L)) := sorry

/-- Degreewise pullback of unbounded cochain complexes is canonically strong monoidal. -/
@[implicit_reducible]
noncomputable def modulePullbackComplex.monoidal :
    f.modulePullbackComplex.Monoidal :=
  @Functor.Monoidal.ofLaxMonoidal _ _ _ _ _ _
    f.modulePullbackComplex
    (@Functor.Cochain.laxMonoidal _ _ _ _ _ _ _ _ _ _ _ _
      f.modulePullback (modulePullback_additive f) (modulePullback.monoidal f)
      _ _ _ _ _ _ _ _ (modulePullback.hasMappedTensorTotals f))
    (@Functor.Cochain.unitIso _ _ _ _ _ _ _ _ _ _
      f.modulePullback (modulePullback_additive f) (modulePullback.monoidal f)).isIso_hom
    (fun K L ↦ modulePullbackComplex.tensorComparisonIsIso f K L)

/-- Degreewise module pushforward on complexes is canonically lax monoidal as the right adjoint of
strong monoidal complex pullback. -/
@[implicit_reducible]
noncomputable def modulePushforwardComplex.laxMonoidal :
    f.modulePushforwardComplex.LaxMonoidal where
  ε := (modulePullbackPushforwardComplexAdjunction f).homEquiv _ _
    (η f.modulePullbackComplex
      (self := (modulePullbackComplex.monoidal f).toOplaxMonoidal))
  μ K L := (modulePullbackPushforwardComplexAdjunction f).homEquiv _ _
    (δ f.modulePullbackComplex
        (self := (modulePullbackComplex.monoidal f).toOplaxMonoidal)
        ((f.modulePushforwardComplex).obj K) ((f.modulePushforwardComplex).obj L) ≫
      ((modulePullbackPushforwardComplexAdjunction f).counit.app K ⊗ₘ
        (modulePullbackPushforwardComplexAdjunction f).counit.app L))
  μ_natural_left {_ _} _ _ := sorry
  μ_natural_right {_ _} _ _ := sorry
  associativity _ _ _ := sorry
  left_unitality _ := sorry
  right_unitality _ := sorry

/-- The canonical complex pullback-pushforward adjunction is compatible with its monoidal and lax
monoidal structures. -/
theorem modulePullbackPushforwardComplexAdjunction.isMonoidal :
    @Adjunction.IsMonoidal _ _ _ _ _ _ _ _
      (modulePullbackPushforwardComplexAdjunction f)
      (modulePullbackComplex.monoidal f).toOplaxMonoidal
      (modulePushforwardComplex.laxMonoidal f) := sorry

end CommRing

end RingedSite.ToposHom
