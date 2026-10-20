module

public import Mathlib.CategoryTheory.CommSq
public import Mathlib.CategoryTheory.Limits.Preserves.Shapes.Kernels
public import Mathlib.CategoryTheory.Sites.CartesianMonoidal
public import Mathlib.CategoryTheory.Sites.DenseSubsite.Basic
public import ReasLib.Algebra.Category.ModuleCat.Sheaf.RingedSite.Tensor.Bilinear
public import ReasLib.Algebra.Category.ModuleCat.Sheaf.RingedSite.Tensor.Sections
public import Mathlib.CategoryTheory.Types.Basic
public import ReasLib.AlgebraicGeometry.Scheme.Module.Monoidal
public import ReasLib.AlgebraicGeometry.Scheme.Module.Pullback.Monoidal
public import ReasLib.AlgebraicGeometry.Scheme.ProjectiveBundle.ConormalAtlas
public import ReasLib.CategoryTheory.Sites.Topos.ModuleAdjunction
public import stacks_project.Chap65.Lemma_65_12_4_Immersion
public import stacks_project.Chap66.Lemma_66_16_4_Etale
public import stacks_project.Chap66.Lemma_66_18_8_Pullback
public import stacks_project.Chap66.«66_26_0_1_Pushforward»
public import stacks_project.Chap66.«66_27_0_1_Comparison»
public import stacks_project.Chap67.Lemma_67_13_7_ProjectionFormula
public import stacks_project.Chap67.Lemma_67_14_1_Quotient
public import stacks_project.Chap67.Lemma_67_28_12_IdealSheaf
public import stacks_project.Chap69.Lemma_69_13_2_IdealPower
public import stacks_project.Chap69.Lemma_69_17_2_Pullback
public import ReasLib.AlgebraicGeometry.RingedSpace.Module.TensorUnit
public import stacks_project.Chap66.«66_26_1_1_Restrict»
public import stacks_project.Chap71.Lemma_71_16_4_Presentation
public import stacks_project.Chap76.Definition_76_6_5_Conormal
import stacks_project.Chap76.Lemma_76_5_3_Map
public import stacks_project.Chap76.Lemma_76_5_4_Comparison

/-!
# Canonical conormal comparisons for projective bundles of algebraic spaces

The conormal sheaf of a closed immersion of algebraic spaces is `Hom.conormalSheaf`.
A commutative square of immersions induces `Hom.Conormal.map`. The tautological
kernel-tensor-inverse of a symmetric projective bundle is compared with this sheaf
by descending the scheme atlas map along the étale covering of the total space.
-/

@[expose] public section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits Opposite
open CategoryTheory.MonoidalCategory
open CategoryTheory.CartesianMonoidalCategory
open CategoryTheory.ExactPairing
open CategoryTheory.MonoidalCategory.isInvertibleObject
open CategoryTheory.InvertibleQuotient hiding pullback pullbackClass
open CategoryTheory.Sheaf.InternalModule
open AlgebraicGeometry.AlgebraicSpace
open AlgebraicGeometry.AlgebraicSpace.ProjectiveBundle
open AlgebraicGeometry.AlgebraicSpace.Modules
open SheafOfModules.RingedSite
open scoped TensorProduct

noncomputable section

universe u

namespace AlgebraicGeometry.AlgebraicSpace.Modules

variable {S : Scheme.{u}}

/-- Scheme modules on the underlying scheme of an object of `Over S` carry the canonical
scheme-module tensor product. -/
instance instMonoidalCategory_overLeft (U : Over S) :
    MonoidalCategory U.left.Modules :=
  Scheme.Modules.instMonoidalCategory U.left

/-- Pullback of the monoidal unit along `h`. -/
def pullbackMonoidalUnitIso {Y Z : AlgebraicSpace S} (h : Z ⟶ Y) :
    (pullback h).obj (𝟙_ Y.Modules) ≅ 𝟙_ Z.Modules :=
  (pullback h).mapIso (structureModuleIsoTensorUnit Y).symm ≪≫
    { hom := IdealSubobject.pullbackUnit h
      inv := structureModulePullbackInv h
      hom_inv_id := sorry
      inv_hom_id := sorry } ≪≫
    structureModuleIsoTensorUnit Z

/-- The type-valued sheaf on the small étale site underlying an algebraic-space module. -/
def moduleUnderlying {Y : AlgebraicSpace S} (M : Y.Modules) :
    Sheaf (smallEtaleTopology Y) (Type u) :=
  (ToInternal.underlying (structureSheaf Y)).obj M

/-- Transport a morphism of commutative presentations to a morphism of `Y.Modules`. -/
def modulesTensorHom {Y : AlgebraicSpace S} {F G H : Y.Modules}
    (φ : (toCommModules Y).obj F ⊗ (toCommModules Y).obj G ⟶ (toCommModules Y).obj H) :
    F ⊗ G ⟶ H :=
  (ofCommModules Y).map φ ≫ (commModulesEquivalence Y).counitIso.hom.app H

/-- Pointwise pure tensor of commutative module sections. -/
def commPointwiseTensor {Y : AlgebraicSpace S} {A B : commModules Y}
    (U : (smallEtaleSite Y)ᵒᵖ) (x : A.val.obj U) (y : B.val.obj U) :
    (PresheafOfModules.Monoidal.tensorObj A.val B.val).obj U :=
  x ⊗ₜ y

/-- Sheaf morphism from the sheafified pointwise tensor of `toComm F` and `toComm G` to
`toComm (F ⊗ G)`. -/
def commTensorComparison {Y : AlgebraicSpace S} (F G : Y.Modules) :
    (moduleSheafification.{u + 1, u, u, u} (commStructureSheaf Y)).obj
      (PresheafOfModules.Monoidal.tensorObj
        ((toCommModules Y).obj F).val
        ((toCommModules Y).obj G).val) ⟶
      (toCommModules Y).obj (F ⊗ G) :=
  (Functor.Monoidal.μIso
      (moduleSheafification.{u + 1, u, u, u} (commStructureSheaf Y))
      ((toCommModules Y).obj F).val
      ((toCommModules Y).obj G).val).inv ≫
    tensorHom
      (moduleSheafificationValIso.{u + 1, u, u, u} (commStructureSheaf Y)
        ((toCommModules Y).obj F)).hom
      (moduleSheafificationValIso.{u + 1, u, u, u} (commStructureSheaf Y)
        ((toCommModules Y).obj G)).hom ≫
    (commModulesEquivalence Y).unit.app
      ((toCommModules Y).obj F ⊗ (toCommModules Y).obj G)

/-- Pure tensor of commutative presentations, transported to `toComm (M ⊗ N)`. -/
def commTensorSection {Y : AlgebraicSpace S} (M N : Y.Modules)
    {U : (smallEtaleSite Y)ᵒᵖ}
    (x : ((toCommModules Y).obj M).val.obj U)
    (y : ((toCommModules Y).obj N).val.obj U) :
    ((toCommModules Y).obj (M ⊗ N)).val.obj U :=
  (commTensorComparison M N).val.app U
    ((moduleSheafificationUnitToVal.{u + 1, u, u, u} (commStructureSheaf Y)
        (PresheafOfModules.Monoidal.tensorObj
          ((toCommModules Y).obj M).val
          ((toCommModules Y).obj N).val)).app U
      (commPointwiseTensor U x y))

/-- View an underlying type-valued section as a module section, via `ToInternal.sectionEquiv`. -/
def ofUnderlyingSection {Y : AlgebraicSpace S} (M : Y.Modules)
    {U : (smallEtaleSite Y)ᵒᵖ} (s : (moduleUnderlying M).obj.obj U) :
    M.val.obj U :=
  ToInternal.sectionEquiv (structureSheaf Y) M U s

/-- View a module section as an underlying type-valued section, via `ToInternal.sectionEquiv`. -/
def toUnderlyingSection {Y : AlgebraicSpace S} (M : Y.Modules)
    {U : (smallEtaleSite Y)ᵒᵖ} (s : M.val.obj U) :
    (moduleUnderlying M).obj.obj U :=
  (ToInternal.sectionEquiv (structureSheaf Y) M U).symm s

/-- View a module section as a section of its commutative presentation, via the
restriction-of-scalars equivalence `commModulesEquivalence`. -/
def asCommSection {Y : AlgebraicSpace S} (M : Y.Modules)
    {U : (smallEtaleSite Y)ᵒᵖ} (s : M.val.obj U) :
    ((toCommModules Y).obj M).val.obj U :=
  ((toCommModules Y).map
      ((commModulesEquivalence Y).counitIso.inv.app M)).val.app U
    ((ToInternal.sectionEquiv (structureSheaf Y)
        ((ofCommModules Y).obj ((toCommModules Y).obj M)) U).symm
      (((ToInternal.underlying (structureSheaf Y)).map
          ((commModulesEquivalence Y).counitIso.inv.app M)).hom.app U
        (toUnderlyingSection M s)))

/-- View a commutative presentation section as a section of the original module. -/
def ofCommSection {Y : AlgebraicSpace S} (M : Y.Modules)
    {U : (smallEtaleSite Y)ᵒᵖ} (s : ((toCommModules Y).obj M).val.obj U) :
    M.val.obj U :=
  ofUnderlyingSection M
    (((ToInternal.underlying (structureSheaf Y)).map
        ((commModulesEquivalence Y).counitIso.hom.app M)).hom.app U
      (ToInternal.sectionEquiv (structureSheaf Y)
        ((ofCommModules Y).obj ((toCommModules Y).obj M)) U s))

/-- The type-valued sheaf morphism sending a pair of local sections to their pure tensor. -/
def tensorSectionUnderlying {Z : AlgebraicSpace S} (M N : Z.Modules) :
    moduleUnderlying M ⊗ moduleUnderlying N ⟶ moduleUnderlying (M ⊗ N) where
  hom :=
    { app := fun U ↦
        TypeCat.ofHom fun p ↦
          toUnderlyingSection (M ⊗ N)
            (ofCommSection (M ⊗ N)
              (commTensorSection M N
                (asCommSection M
                  (ofUnderlyingSection M
                    ((fst (moduleUnderlying M) (moduleUnderlying N)).hom.app U p)))
                (asCommSection N
                  (ofUnderlyingSection N
                    ((snd (moduleUnderlying M) (moduleUnderlying N)).hom.app U p)))))
      naturality := fun _ _ _ ↦ sorry }

/-- The cartesian type-valued comparison `h_* M × h_* N ⟶ h_*(M ⊗ N)`. -/
def pushforwardTensorUnderlying {Y Z : AlgebraicSpace S} (h : Z ⟶ Y)
    (M N : Z.Modules) :
    moduleUnderlying ((pushforward h).obj M) ⊗
      moduleUnderlying ((pushforward h).obj N) ⟶
      moduleUnderlying ((pushforward h).obj (M ⊗ N)) :=
  ((RingedSite.ToposHom.ModulePushforward.forgetIso (ringedToposHom h)).hom.app M ⊗ₘ
      (RingedSite.ToposHom.ModulePushforward.forgetIso (ringedToposHom h)).hom.app N) ≫
    typePushforward_prodLax h (moduleUnderlying M) (moduleUnderlying N) ≫
      (typePushforward h).map (tensorSectionUnderlying M N) ≫
        (RingedSite.ToposHom.ModulePushforward.forgetIso (ringedToposHom h)).inv.app (M ⊗ N)

/-- Compatible bilinear map of commutative presentations representing the pushforward
tensorator. -/
def pushforwardTensorBilinear {Y Z : AlgebraicSpace S} (h : Z ⟶ Y) (M N : Z.Modules) :
    PresheafOfModules.BilinearMap (commStructureSheaf Y).obj
      ((toCommModules Y).obj ((pushforward h).obj M)).val
      ((toCommModules Y).obj ((pushforward h).obj N)).val
      ((toCommModules Y).obj ((pushforward h).obj (M ⊗ N))).val where
  app U :=
    { toFun := fun x ↦
        { toFun := fun y ↦
            asCommSection ((pushforward h).obj (M ⊗ N))
              (ofUnderlyingSection ((pushforward h).obj (M ⊗ N))
                ((pushforwardTensorUnderlying h M N).hom.app U
                  (toUnderlyingSection ((pushforward h).obj M) (ofCommSection _ x),
                    toUnderlyingSection ((pushforward h).obj N) (ofCommSection _ y))))
          map_add' := fun _ _ ↦ sorry
          map_smul' := fun _ _ ↦ sorry }
      map_add' := fun _ _ ↦ sorry
      map_smul' := fun _ _ ↦ sorry }
  naturality _ _ _ := sorry

/-- The lax comparison `(h_* M) ⊗ (h_* N) ⟶ h_*(M ⊗ N)`. -/
def pushforwardTensorLax {Y Z : AlgebraicSpace S} (h : Z ⟶ Y) (M N : Z.Modules) :
    (pushforward h).obj M ⊗ (pushforward h).obj N ⟶
      (pushforward h).obj (M ⊗ N) :=
  modulesTensorHom
    (tensorHom
        (moduleSheafificationValIso.{u + 1, u, u, u} (commStructureSheaf Y)
          ((toCommModules Y).obj ((pushforward h).obj M))).inv
        (moduleSheafificationValIso.{u + 1, u, u, u} (commStructureSheaf Y)
          ((toCommModules Y).obj ((pushforward h).obj N))).inv ≫
      Functor.LaxMonoidal.μ
        (moduleSheafification.{u + 1, u, u, u} (commStructureSheaf Y))
        ((toCommModules Y).obj ((pushforward h).obj M)).val
        ((toCommModules Y).obj ((pushforward h).obj N)).val ≫
      (moduleSheafification.{u + 1, u, u, u} (commStructureSheaf Y)).map
        (PresheafOfModules.BilinearMap.toHom (pushforwardTensorBilinear h M N)) ≫
      (moduleSheafificationValIso.{u + 1, u, u, u} (commStructureSheaf Y)
        ((toCommModules Y).obj ((pushforward h).obj (M ⊗ N)))).hom)

/-- The oplax comparison `h^*(A ⊗ B) ⟶ h^* A ⊗ h^* B`, the adjunction transpose of the
tensor of units followed by `pushforwardTensorLax`. -/
def pullbackTensorOplax {Y Z : AlgebraicSpace S} (h : Z ⟶ Y) (A B : Y.Modules) :
    (pullback h).obj (A ⊗ B) ⟶ (pullback h).obj A ⊗ (pullback h).obj B :=
  ((pullbackPushforwardAdjunction h).homEquiv
      (A ⊗ B)
      ((pullback h).obj A ⊗ (pullback h).obj B)).symm
    (((pullbackPushforwardAdjunction h).unit.app A ⊗ₘ
        (pullbackPushforwardAdjunction h).unit.app B) ≫
      pushforwardTensorLax h ((pullback h).obj A) ((pullback h).obj B))

/-- The oplax pullback-tensor comparison is an isomorphism. -/
instance instIsIso_pullbackTensorOplax {Y Z : AlgebraicSpace S} (h : Z ⟶ Y)
    (A B : Y.Modules) :
    IsIso (pullbackTensorOplax h A B) :=
  sorry

/-- The canonical isomorphism `h^*(A ⊗ B) ≅ h^* A ⊗ h^* B`. -/
def pullbackTensorIso {Y Z : AlgebraicSpace S} (h : Z ⟶ Y) (A B : Y.Modules) :
    (pullback h).obj (A ⊗ B) ≅ (pullback h).obj A ⊗ (pullback h).obj B :=
  asIso (pullbackTensorOplax h A B)

/-- The lax comparison `h^* A ⊗ h^* B ⟶ h^*(A ⊗ B)`. -/
def pullbackTensorLax {Y Z : AlgebraicSpace S} (h : Z ⟶ Y) (A B : Y.Modules) :
    (pullback h).obj A ⊗ (pullback h).obj B ⟶ (pullback h).obj (A ⊗ B) :=
  (pullbackTensorIso h A B).inv

/-- Restriction of modules from `ofOver U` to the underlying scheme preserves zero morphisms. -/
instance preservesZeroMorphisms_restrictToScheme (U : Over S) :
    (restrictToScheme U).PreservesZeroMorphisms :=
  sorry

/-- The functor sending an open of `U.left` to the corresponding small-étale object of
`ofOver U`. -/
def openAsEtale (U : Over S) : U.left.Opens ⥤ smallEtaleSite (ofOver U) :=
  Scheme.smallZariskiOpenFunctor U.left ⋙
    Scheme.SiteRestriction.smallZariskiToSmallEtale U.left ⋙
    schemeEtaleToSmallEtale U

/-- Zariski opens are cover-dense in the small étale site of a scheme, viewed as an
algebraic space. -/
instance instIsCoverDense_openAsEtale (U : Over S) :
    (openAsEtale U).IsCoverDense (smallEtaleTopology (ofOver U)) :=
  sorry

/-- Zariski opens are locally full in the small étale site of a scheme, viewed as an
algebraic space. -/
instance instIsLocallyFull_openAsEtale (U : Over S) :
    (openAsEtale U).IsLocallyFull (smallEtaleTopology (ofOver U)) :=
  sorry

/-- An étale covering morphism is cover-dense on small étale sites via postcomposition. -/
instance instIsCoverDense_restrictPostcompose {Y Z : AlgebraicSpace S} (h : Z ⟶ Y)
    [Etale h] :
    (restrictPostcompose h).IsCoverDense (smallEtaleTopology Y) :=
  sorry

/-- An étale covering morphism is locally full on small étale sites via postcomposition. -/
instance instIsLocallyFull_restrictPostcompose {Y Z : AlgebraicSpace S} (h : Z ⟶ Y)
    [Etale h] :
    (restrictPostcompose h).IsLocallyFull (smallEtaleTopology Y) :=
  sorry

/-- The type-valued sheaf on opens underlying a scheme module. -/
def schemeOpensUnderlying (Y : Scheme.{u}) (N : Y.Modules) :
    (Y.Opens)ᵒᵖ ⥤ Type u :=
  ((ToInternal.underlying Y.ringCatSheaf).obj N).obj

/-- Whisker a morphism of restricted scheme modules along `openAsEtale`. -/
def restrictOpensTypeHom {U : Over S} {A B : (ofOver U).Modules}
    (φ : (restrictToScheme U).obj A ⟶ (restrictToScheme U).obj B) :
    schemeOpensUnderlying U.left ((restrictToScheme U).obj A) ⟶
      schemeOpensUnderlying U.left ((restrictToScheme U).obj B) :=
  ((ToInternal.underlying U.left.ringCatSheaf).map φ).hom

/-- A restricted scheme-module section, viewed on the corresponding open-as-étale object. -/
def ofRestrictSection {U : Over S} (A : (ofOver U).Modules)
    {V : (U.left.Opens)ᵒᵖ}
    (s : ((restrictToScheme U).obj A).val.obj V) :
    A.val.obj (op ((openAsEtale U).obj V.unop)) :=
  ((SmallEtaleModuleGlueing.restrictFunctorId (ofOver U)).hom.app A).val.app
    (op ((openAsEtale U).obj V.unop))
    ((Hom.Conormal.restrictToSchemeOpensIso A).hom.val.app V s)

/-- An algebraic-space section on an open-as-étale object, viewed as a restricted
scheme-module section. -/
def toRestrictSection {U : Over S} (A : (ofOver U).Modules)
    {V : (U.left.Opens)ᵒᵖ}
    (s : A.val.obj (op ((openAsEtale U).obj V.unop))) :
    ((restrictToScheme U).obj A).val.obj V :=
  (Hom.Conormal.restrictToSchemeOpensIso A).inv.val.app V
    (((SmallEtaleModuleGlueing.restrictFunctorId (ofOver U)).inv.app A).val.app
      (op ((openAsEtale U).obj V.unop)) s)

/-- Restricted scheme-module sections, compared with algebraic-space sections on the
corresponding open-as-étale object. -/
def restrictOpensUnderlyingHom {U : Over S} (A : (ofOver U).Modules) :
    (openAsEtale U).op ⋙ (moduleUnderlying A).obj ⟶
      schemeOpensUnderlying U.left ((restrictToScheme U).obj A) where
  app V := ↾fun s ↦ toRestrictSection A s
  naturality := fun _ _ _ ↦ sorry

/-- Algebraic-space sections on an open-as-étale object, compared with restricted
scheme-module sections. -/
def restrictOpensUnderlyingInv {U : Over S} (A : (ofOver U).Modules) :
    schemeOpensUnderlying U.left ((restrictToScheme U).obj A) ⟶
      (openAsEtale U).op ⋙ (moduleUnderlying A).obj where
  app V := ↾fun s ↦ ofRestrictSection A s
  naturality := fun _ _ _ ↦ sorry

/-- Lift a morphism of restricted scheme modules to a morphism of algebraic-space modules on
`ofOver U` by cover-dense extension along `openAsEtale`. -/
def restrictToSchemePreimage {U : Over S} {A B : (ofOver U).Modules}
    (φ : (restrictToScheme U).obj A ⟶ (restrictToScheme U).obj B) :
    A ⟶ B :=
  homOfUnderlying (structureSheaf (ofOver U))
    ⟨Functor.IsCoverDense.sheafHom
      (restrictOpensUnderlyingHom A ≫ restrictOpensTypeHom φ ≫
        restrictOpensUnderlyingInv B)⟩
    sorry sorry

/-- Kernel comparison for restriction of modules from `ofOver U` to the underlying scheme. -/
def restrictKernelComparison {U : Over S} {A B : (ofOver U).Modules} (f : A ⟶ B) :
    (restrictToScheme U).obj (kernel f) ⟶ kernel ((restrictToScheme U).map f) :=
  kernelComparison f (restrictToScheme U)

/-- Restriction of modules preserves kernels of module morphisms. -/
instance instIsIso_restrictKernelComparison {U : Over S} {A B : (ofOver U).Modules}
    (f : A ⟶ B) :
    IsIso (restrictKernelComparison f) :=
  sorry

/-- The sectionwise bilinear map presenting restriction of a tensor product. -/
def restrictTensorBilinear {U : Over S} (A B : (ofOver U).Modules) :
    SheafOfModules.RingedSite.SectionBilinearMap.{u, u} U.left.sheaf
      ((restrictToScheme U).obj A) ((restrictToScheme U).obj B)
      ((restrictToScheme U).obj (A ⊗ B)) where
  app V :=
    { toFun := fun x ↦
        { toFun := fun y ↦
            toRestrictSection (A ⊗ B)
              (ofCommSection (A ⊗ B)
                (commTensorSection A B
                  (asCommSection A (ofRestrictSection A x))
                  (asCommSection B (ofRestrictSection B y))))
          map_add' := fun _ _ ↦ sorry
          map_smul' := fun _ _ ↦ sorry }
      map_add' := fun _ _ ↦ sorry
      map_smul' := fun _ _ ↦ sorry }
  naturality _ _ _ := sorry

/-- The lax comparison `restrict A ⊗ restrict B ⟶ restrict(A ⊗ B)`. -/
def restrictTensorLax {U : Over S} (A B : (ofOver U).Modules) :
    ((restrictToScheme U).obj A ⊗ (restrictToScheme U).obj B : U.left.Modules) ⟶
      (restrictToScheme U).obj (A ⊗ B) :=
  (restrictTensorBilinear A B).hom

/-- The lax restriction-tensor comparison is an isomorphism. -/
instance instIsIso_restrictTensorLax {U : Over S} (A B : (ofOver U).Modules) :
    IsIso (restrictTensorLax A B) :=
  sorry

/-- The canonical isomorphism `restrict A ⊗ restrict B ≅ restrict(A ⊗ B)`. -/
def restrictTensorIso {U : Over S} (A B : (ofOver U).Modules) :
    ((restrictToScheme U).obj A ⊗ (restrictToScheme U).obj B : U.left.Modules) ≅
      (restrictToScheme U).obj (A ⊗ B) :=
  asIso (restrictTensorLax A B)

/-- The oplax comparison `restrict(A ⊗ B) ⟶ restrict A ⊗ restrict B`. -/
def restrictTensorOplax {U : Over S} (A B : (ofOver U).Modules) :
    (restrictToScheme U).obj (A ⊗ B) ⟶
      ((restrictToScheme U).obj A ⊗ (restrictToScheme U).obj B : U.left.Modules) :=
  (restrictTensorIso A B).inv

/-- Restriction of the monoidal unit. -/
def restrictMonoidalUnitIso (U : Over S) :
    (restrictToScheme U).obj (𝟙_ (ofOver U).Modules) ≅ 𝟙_ U.left.Modules :=
  (restrictToScheme U).mapIso (structureModuleIsoTensorUnit (ofOver U)).symm ≪≫
    (@asIso _ _ _ _ (Hom.Conormal.schemeUnitToRestrictedUnit U)
      (Hom.Conormal.schemeUnitToRestrictedUnit_isIso U)).symm ≪≫
    RingedSpace.unitIsoTensorUnit U.left.toRingedSpace

/-- The image pairing of an invertible module under restriction to the underlying scheme. -/
@[implicit_reducible]
def restrictImagePairing {U : Over S} (L : (ofOver U).Modules) [isInvertibleObject L] :
    ExactPairing ((restrictToScheme U).obj L)
      ((restrictToScheme U).obj (inverse L)) where
  coevaluation' :=
    (restrictMonoidalUnitIso U).inv ≫
      (restrictToScheme U).map (exactPairing L).coevaluation' ≫
        restrictTensorOplax L (inverse L)
  evaluation' :=
    restrictTensorLax (inverse L) L ≫
      (restrictToScheme U).map (exactPairing L).evaluation' ≫
        (restrictMonoidalUnitIso U).hom
  coevaluation_evaluation' := sorry
  evaluation_coevaluation' := sorry

/-- Restriction of a chosen tensor inverse compared with the chosen inverse of the restriction. -/
def restrictInverseComparison {U : Over S} (L : (ofOver U).Modules)
    [isInvertibleObject L] [isInvertibleObject ((restrictToScheme U).obj L)] :
    (restrictToScheme U).obj (inverse L) ⟶ inverse ((restrictToScheme U).obj L) :=
  (rightDualIso (restrictImagePairing L)
      (exactPairing ((restrictToScheme U).obj L))).hom

/-- The restriction comparison of chosen inverses is an isomorphism. -/
instance instIsIso_restrictInverseComparison {U : Over S} (L : (ofOver U).Modules)
    [isInvertibleObject L] [isInvertibleObject ((restrictToScheme U).obj L)] :
    IsIso (restrictInverseComparison L) :=
  sorry

end AlgebraicGeometry.AlgebraicSpace.Modules

namespace AlgebraicGeometry
namespace AlgebraicSpace
namespace ProjectiveBundle
namespace SymmetricPresentation

variable {S : Scheme.{u}} {X P : AlgebraicSpace S} {ℰ : X.Modules} [ℰ.IsQuasicoherent]
variable {π : P ⟶ X} (Pres : SymmetricPresentation π ℰ)

/-- The base-changed section of a lift through a presented projective bundle is a closed
immersion. -/
instance instIsClosedImmersion_baseChangeSection {T : AlgebraicSpace S}
    {f : T ⟶ X} (σ : Lift π f) :
    IsClosedImmersion σ.baseChangeSection := sorry


/-- The identity-base-change transport of an invertible quotient representative. -/
def sectionPullbackQuotient (q : InvertibleQuotient ℰ) :
    InvertibleQuotient ((Modules.pullback (𝟙 X)).obj ℰ) :=
  precomposeIso ((SmallEtaleModuleGlueing.modulesPullbackId X).app ℰ) q

/-- The identity-pullback transport of an invertible quotient commutes with the source
isomorphism. -/
theorem sectionPullbackQuotient_comm (q : InvertibleQuotient ℰ) :
    q.hom ≫ (Iso.refl q.object).hom =
      ((SmallEtaleModuleGlueing.modulesPullbackId X).app ℰ).symm.hom ≫
        (sectionPullbackQuotient q).hom := sorry

/-- A quotient representing the class of a section continues to represent its concrete
tautological quotient after the canonical identity-pullback transport. -/
theorem sectionPullbackQuotient_class (σ : Lift π (𝟙 X))
    (q : InvertibleQuotient ℰ)
    (h : IsoClass.mk q = Pres.sectionToQuotientClass σ) :
    IsoClass.mk (sectionPullbackQuotient q) =
      IsoClass.mk (Pres.liftSourceQuotient σ) := sorry

/-- Compatible source and target isomorphisms induce an isomorphism of conormal objects. -/
def conormalIsoOf {T : AlgebraicSpace S} {E E' : T.Modules}
    (q : InvertibleQuotient E) (q' : InvertibleQuotient E')
    (sourceIso : E ≅ E') (targetIso : q.object ≅ q'.object)
    (comm : q.hom ≫ targetIso.hom = sourceIso.hom ≫ q'.hom) :
    conormalObject q ≅ conormalObject q' :=
  conormalObjectIso q q' sourceIso targetIso comm

/-- Two invertible quotients of the same module that determine the same class have canonically
isomorphic conormal objects. -/
def conormalIsoOfMkEq {T : AlgebraicSpace S} {E : T.Modules}
    {q q' : InvertibleQuotient E} (h : IsoClass.mk q = IsoClass.mk q') :
    conormalObject q ≅ conormalObject q' :=
  conormalIsoOf q q' (Iso.refl _) (targetIsoOfMkEq h) (targetIsoOfMkEq_spec h)

/-- The conormal object of a section quotient is canonically identified with that of its
identity-base-change transport. -/
def sectionPullbackConormalIso (q : InvertibleQuotient ℰ) :
    conormalObject q ≅ conormalObject (sectionPullbackQuotient q) :=
  conormalIsoOf q (sectionPullbackQuotient q)
    ((SmallEtaleModuleGlueing.modulesPullbackId X).app ℰ).symm (Iso.refl _)
    (sectionPullbackQuotient_comm q)

/-- The canonical morphism from a projective bundle to its base change along the identity of
the base. -/
def sectionAmbientMap : P ⟶ pullback π (𝟙 X) :=
  pullback.lift (𝟙 P) π ((Category.id_comp π).trans (Category.comp_id π).symm)

/-- A section and its identity-base-change section form the canonical ambient square. -/
theorem sectionConormalSquare (σ : Lift π (𝟙 X)) :
    CommSq (𝟙 X) σ.hom σ.baseChangeSection (sectionAmbientMap (π := π)) := sorry

/-- The conormal sheaf of the identity-base-change section maps canonically to the conormal
sheaf of the original section. -/
def sectionConormalTransport (σ : Lift π (𝟙 X)) [IsImmersion σ.hom] :
    Hom.conormalSheaf σ.baseChangeSection ⟶ Hom.conormalSheaf σ.hom :=
  (SmallEtaleModuleGlueing.modulesPullbackId X).inv.app
      (Hom.conormalSheaf σ.baseChangeSection) ≫
    Hom.Conormal.map (sectionConormalSquare (π := π) σ)

/-- The canonical isomorphism from the conormal object of a representative to that of the
concrete quotient attached to the same lift. -/
def liftConormalRepresentativeIso {T : AlgebraicSpace S} {f : T ⟶ X} (σ : Lift π f)
    (q : InvertibleQuotient ((Modules.pullback f).obj ℰ))
    (h : IsoClass.mk q = IsoClass.mk (Pres.liftSourceQuotient σ)) :
    conormalObject q ≅ conormalObject (Pres.liftSourceQuotient σ) :=
  conormalIsoOfMkEq h

/-- The local covering morphism is étale. -/
instance instEtale_localCoverHom : Etale Pres.localCoverHom := sorry

/-- Quasi-coherence of the local chart module. -/
instance instIsQuasicoherent_localℰ : Pres.localℰ.IsQuasicoherent :=
  Pres.localℰ_isQuasicoherent

/-- The identity lift of the local scheme presentation. -/
def localIdentityLift :
    AlgebraicGeometry.Scheme.ProjectiveBundle.Lift Pres.localπ Pres.localπ :=
  AlgebraicGeometry.Scheme.ProjectiveBundle.Lift.identity Pres.localπ

/-- The scheme-level kernel-tensor-inverse to conormal-sheaf map of the local identity
lift, obtained from the homogeneous-coordinate atlas of `localPresentation`. -/
def localIdentityConormalMap :
    CategoryTheory.InvertibleQuotient.conormalObject
      (Pres.localPresentation.liftSourceQuotient Pres.localπ Pres.localIdentityLift) ⟶
    AlgebraicGeometry.Scheme.Hom.conormalSheaf Pres.localIdentityLift.baseChangeSection :=
  AlgebraicGeometry.Scheme.ProjectiveBundle.SymmetricPresentation.ConormalAtlas.map
    (AlgebraicGeometry.Scheme.ProjectiveBundle.SymmetricPresentation.ConormalAtlas.ofPresentation
      Pres.localPresentation)
    Pres.localπ Pres.localIdentityLift

/-- The local scheme atlas conormal map is an isomorphism. -/
theorem localIdentityConormalMap_isIso :
    IsIso Pres.localIdentityConormalMap := sorry

/-- The étale chart of the total space, as an object of `Over S`. -/
abbrev localCoverOver : Over S :=
  Over.mk (Pres.localπ ≫ Pres.atlas.left.hom)

/-- The module category of the local covering scheme carries the canonical scheme-module
tensor product. -/
instance instMonoidalCategory_localScheme :
    MonoidalCategory Pres.localScheme.Modules :=
  Scheme.Modules.instMonoidalCategory Pres.localScheme

/-- The module category of `localCoverOver.left` is the same canonical scheme-module tensor. -/
instance instMonoidalCategory_localCoverOver :
    MonoidalCategory Pres.localCoverOver.left.Modules :=
  Scheme.Modules.instMonoidalCategory Pres.localCoverOver.left


/-- The image pairing of an invertible module under algebraic-space module pullback. -/
@[implicit_reducible]
def pullbackImagePairing {Y Z : AlgebraicSpace S} (h : Y ⟶ Z)
    (L : Z.Modules) [isInvertibleObject L] :
    ExactPairing ((Modules.pullback h).obj L)
      ((Modules.pullback h).obj (inverse L)) where
  coevaluation' :=
    (pullbackMonoidalUnitIso h).inv ≫
      (Modules.pullback h).map (exactPairing L).coevaluation' ≫
        pullbackTensorOplax h L (inverse L)
  evaluation' :=
    pullbackTensorLax h (inverse L) L ≫
      (Modules.pullback h).map (exactPairing L).evaluation' ≫
        (pullbackMonoidalUnitIso h).hom
  coevaluation_evaluation' := sorry
  evaluation_coevaluation' := sorry

/-- Pullback of a chosen tensor inverse compared with the chosen inverse of the pullback. -/
def pullbackInverseComparison {Y Z : AlgebraicSpace S} (h : Y ⟶ Z)
    (L : Z.Modules) [isInvertibleObject L]
    [isInvertibleObject ((Modules.pullback h).obj L)] :
    (Modules.pullback h).obj (inverse L) ⟶ inverse ((Modules.pullback h).obj L) :=
  (rightDualIso (pullbackImagePairing h L)
      (exactPairing ((Modules.pullback h).obj L))).hom

/-- The ambient comparison from the base change along `g ≫ f` to the base change along `f`. -/
def precompAmbientMap {T R : AlgebraicSpace S} {f : T ⟶ X} (_σ : Lift π f) (g : R ⟶ T) :
    pullback π (g ≫ f) ⟶ pullback π f :=
  pullback.lift (pullback.fst π (g ≫ f)) (pullback.snd π (g ≫ f) ≫ g)
    ((pullback.condition (f := π) (g := g ≫ f)).trans
      (Category.assoc (pullback.snd π (g ≫ f)) g f).symm)

/-- Canonical comparison from the pullback of a quotient conormal object to the conormal object
of the pulled-back quotient. -/
def pullbackConormalObjectComparison {Y Z : AlgebraicSpace S} (h : Y ⟶ Z)
    {E : Z.Modules} (q : InvertibleQuotient E) :
    (Modules.pullback h).obj (conormalObject q) ⟶
      conormalObject (pullbackQuotient h q) :=
  pullbackTensorOplax h (kernel q.hom)
      (@isInvertibleObject.inverse _ _ _ q.object q.isInvertible) ≫
    (kernelComparison q.hom (Modules.pullback h) ⊗ₘ
      @pullbackInverseComparison S Y Z h q.object q.isInvertible
        (pullbackQuotient h q).isInvertible)

/-- The pullback comparison on conormal objects is an isomorphism. -/
instance instIsIso_pullbackConormalObjectComparison {Y Z : AlgebraicSpace S}
    (h : Y ⟶ Z) {E : Z.Modules} (q : InvertibleQuotient E) :
    IsIso (pullbackConormalObjectComparison h q) := sorry

/-- The local covering morphism is an immersion of the local scheme into the total space,
as a morphism of schemes over `S` after viewing the identity section of the chart. -/
instance instIsImmersion_localIdentitySection :
    AlgebraicGeometry.IsImmersion Pres.localIdentityLift.baseChangeSection :=
  sorry

/-- The ambient scheme of the local identity section, as an object of `Over S`. -/
def localIdentityAmbientOver : Over S :=
  Over.mk
    (Limits.pullback.fst Pres.localπ Pres.localπ ≫ Pres.localπ ≫ Pres.atlas.left.hom)

/-- The local identity section, as a morphism in `Over S`. -/
def localIdentitySectionOver : Pres.localCoverOver ⟶ Pres.localIdentityAmbientOver :=
  Over.homMk Pres.localIdentityLift.baseChangeSection sorry

/-- The underlying scheme morphism of the local identity section is an immersion. -/
instance instIsImmersion_localIdentitySectionOver_left :
    AlgebraicGeometry.IsImmersion Pres.localIdentitySectionOver.left :=
  sorry

/-- The covering of the diagonal ambient space by the local scheme pullback. -/
def localIdentityAmbientCover :
    ofOver Pres.localIdentityAmbientOver ⟶ pullback π π :=
  pullback.lift
    (ofOverHomMk (Limits.pullback.fst Pres.localπ Pres.localπ) sorry ≫ Pres.localCoverHom)
    (ofOverHomMk (Limits.pullback.snd Pres.localπ Pres.localπ) sorry ≫ Pres.localCoverHom)
    sorry

/-- The local identity section is a closed immersion of algebraic spaces. -/
instance instIsClosedImmersion_localIdentitySectionOver :
    IsClosedImmersion (ofOverMap Pres.localIdentitySectionOver) :=
  sorry

/-- The square relating the local identity section to the tautological diagonal section. -/
theorem localIdentityConormalSquare :
    CommSq Pres.localCoverHom (ofOverMap Pres.localIdentitySectionOver)
      (Lift.identity π).baseChangeSection Pres.localIdentityAmbientCover :=
  sorry

/-- The conormal comparison of the local identity square is an isomorphism. -/
instance instIsIso_localIdentityConormalMap_square :
    IsIso (Hom.Conormal.map Pres.localIdentityConormalSquare) :=
  sorry

/-- Restriction of the pulled-back diagonal conormal sheaf compared with the scheme
conormal sheaf of the local identity section, via `Hom.Conormal.map` and
`Hom.Conormal.restrictToSchemeIso`. -/
def chartConormalSheafIso :
    (Modules.restrictToScheme Pres.localCoverOver).obj
        ((Modules.pullback Pres.localCoverHom).obj
          (Hom.conormalSheaf (Lift.identity π).baseChangeSection)) ≅
      AlgebraicGeometry.Scheme.Hom.conormalSheaf Pres.localIdentityLift.baseChangeSection :=
  (Modules.restrictToScheme Pres.localCoverOver).mapIso
      (asIso (Hom.Conormal.map Pres.localIdentityConormalSquare)) ≪≫
    Hom.Conormal.restrictToSchemeIso Pres.localIdentitySectionOver

/-- The restricted pulled-back tautological quotient, as an invertible quotient of scheme
modules on the local covering. -/
def restrictTautologicalQuotient :
    InvertibleQuotient
      ((Modules.restrictToScheme Pres.localCoverOver).obj
        ((Modules.pullback Pres.localCoverHom).obj ((Modules.pullback π).obj ℰ)) :
        Pres.localScheme.Modules) where
  object :=
    ((Modules.restrictToScheme Pres.localCoverOver).obj
      ((Modules.pullback Pres.localCoverHom).obj Pres.tautologicalTarget) :
      Pres.localScheme.Modules)
  isInvertible :=
    isInvertibleObject.of_iso Pres.tautologicalRestrictIso.symm
      Pres.localPresentation.tautologicalQuotient.isInvertible
  hom :=
    (Modules.restrictToScheme Pres.localCoverOver).map
      ((Modules.pullback Pres.localCoverHom).map Pres.tautologicalHom)
  hom_epi := sorry

/-- Invertibility of the restricted tautological first twist. -/
instance instIsInvertible_restrictTautologicalTarget :
    isInvertibleObject
      ((Modules.restrictToScheme Pres.localCoverOver).obj
        ((Modules.pullback Pres.localCoverHom).obj Pres.tautologicalTarget)) :=
  Pres.restrictTautologicalQuotient.isInvertible

/-- Invertibility of the tautological first twist after pullback along the local covering. -/
instance instIsInvertible_pullbackTautologicalTarget :
    isInvertibleObject
      ((Modules.pullback Pres.localCoverHom).obj Pres.tautologicalTarget) :=
  (pullbackQuotient Pres.localCoverHom Pres.tautologicalQuotient).isInvertible

/-- Invertibility of the pulled-back tautological quotient target. -/
instance instIsInvertible_pullbackQuotient_tautological :
    isInvertibleObject
      (pullbackQuotient Pres.localCoverHom Pres.tautologicalQuotient).object :=
  Pres.instIsInvertible_pullbackTautologicalTarget

/-- Kernel-tensor comparison after restriction of the pulled-back tautological quotient. -/
def restrictPullbackQuotientKernelTensor :
    ((Modules.restrictToScheme Pres.localCoverOver).obj
        (kernel (pullbackQuotient Pres.localCoverHom Pres.tautologicalQuotient).hom) ⊗
      (Modules.restrictToScheme Pres.localCoverOver).obj
        (@isInvertibleObject.inverse _ _ _
          (pullbackQuotient Pres.localCoverHom Pres.tautologicalQuotient).object
          Pres.instIsInvertible_pullbackQuotient_tautological) :
        Pres.localCoverOver.left.Modules) ⟶
      (kernel ((Modules.restrictToScheme Pres.localCoverOver).map
          (pullbackQuotient Pres.localCoverHom Pres.tautologicalQuotient).hom) ⊗
        @isInvertibleObject.inverse _ _ _
          ((Modules.restrictToScheme Pres.localCoverOver).obj
            (pullbackQuotient Pres.localCoverHom Pres.tautologicalQuotient).object)
          Pres.instIsInvertible_restrictTautologicalTarget :
        Pres.localCoverOver.left.Modules) :=
  Modules.restrictKernelComparison
      (pullbackQuotient Pres.localCoverHom Pres.tautologicalQuotient).hom ⊗ₘ
    @Modules.restrictInverseComparison S Pres.localCoverOver
      (pullbackQuotient Pres.localCoverHom Pres.tautologicalQuotient).object
      Pres.instIsInvertible_pullbackQuotient_tautological
      Pres.instIsInvertible_restrictTautologicalTarget

/-- Restriction of the conormal object of the pulled-back tautological quotient, compared with
the conormal object of the restricted tautological quotient, via kernel and inverse
comparisons. -/
def restrictPullbackQuotientConormalHom :
    (Modules.restrictToScheme Pres.localCoverOver).obj
        (conormalObject (pullbackQuotient Pres.localCoverHom Pres.tautologicalQuotient)) ⟶
      conormalObject Pres.restrictTautologicalQuotient :=
  Modules.restrictTensorOplax
      (kernel (pullbackQuotient Pres.localCoverHom Pres.tautologicalQuotient).hom)
      (@isInvertibleObject.inverse _ _ _
        (pullbackQuotient Pres.localCoverHom Pres.tautologicalQuotient).object
        Pres.instIsInvertible_pullbackQuotient_tautological) ≫
    Pres.restrictPullbackQuotientKernelTensor

/-- The restricted kernel-tensor-inverse comparison is an isomorphism. -/
instance instIsIso_restrictPullbackQuotientConormalHom :
    IsIso (restrictPullbackQuotientConormalHom Pres) :=
  sorry

/-- Restriction of the pulled-back tautological conormal object compared with the conormal
object of the restricted tautological quotient. -/
def restrictPullbackConormalObjectIso :
    ((Modules.restrictToScheme Pres.localCoverOver).obj
        ((Modules.pullback Pres.localCoverHom).obj (conormalObject Pres.tautologicalQuotient)) :
        Pres.localScheme.Modules) ≅
      conormalObject Pres.restrictTautologicalQuotient :=
  (Modules.restrictToScheme Pres.localCoverOver).mapIso
      (asIso (pullbackConormalObjectComparison Pres.localCoverHom Pres.tautologicalQuotient)) ≪≫
    asIso (restrictPullbackQuotientConormalHom Pres)

/-- The restricted tautological quotient, transported by the stored source and target
chart isos, is the scheme tautological quotient. -/
theorem restrictTautologicalQuotient_comm :
    Pres.restrictTautologicalQuotient.hom ≫ Pres.tautologicalRestrictIso.hom =
      Pres.localSourceRestrictIso.hom ≫ Pres.localPresentation.tautologicalMap :=
  Pres.tautologicalHom_restrict

/-- Conormal object of the restricted tautological quotient compared with the scheme
tautological conormal object. -/
def restrictTautologicalConormalObjectIso :=
  @conormalObjectIso Pres.localScheme.Modules
    (inferInstance : Category Pres.localScheme.Modules)
    (Scheme.Modules.instMonoidalCategory Pres.localScheme)
    (inferInstance : Limits.HasZeroMorphisms Pres.localScheme.Modules)
    (inferInstance : Limits.HasKernels Pres.localScheme.Modules)
    _ _ Pres.restrictTautologicalQuotient
    Pres.localPresentation.tautologicalQuotient
    Pres.localSourceRestrictIso Pres.tautologicalRestrictIso
    Pres.restrictTautologicalQuotient_comm

/-- The scheme tautological quotient of the local presentation compared with the identity
lift source quotient. -/
def localIdentityConormalObjectIso :=
  @conormalObjectIso Pres.localScheme.Modules
    (inferInstance : Category Pres.localScheme.Modules)
    (Scheme.Modules.instMonoidalCategory Pres.localScheme)
    (inferInstance : Limits.HasZeroMorphisms Pres.localScheme.Modules)
    (inferInstance : Limits.HasKernels Pres.localScheme.Modules)
    _ _
    Pres.localPresentation.tautologicalQuotient
    (Pres.localPresentation.liftSourceQuotient Pres.localπ Pres.localIdentityLift)
    (Iso.refl _)
    ((Scheme.Modules.pullbackId Pres.localScheme).symm.app
      Pres.localPresentation.tautologicalTarget)
    sorry

/-- Restriction of the pulled-back tautological conormal object compared with the scheme
identity-lift conormal object, as the composite of the pullback/kernel/inverse comparisons
with the stored `tautologicalRestrictIso` and `localSourceRestrictIso`. -/
def chartRestrictConormalObjectIso :=
  Pres.restrictPullbackConormalObjectIso ≪≫
    Pres.restrictTautologicalConormalObjectIso ≪≫
    Pres.localIdentityConormalObjectIso

/-- The scheme atlas map, viewed as a morphism of algebraic-space modules on the local
covering, by Kan-extending the composite of the constructed chart isos with the scheme
atlas map. -/
def localTautologicalPullbackHom :
    (Modules.pullback Pres.localCoverHom).obj (conormalObject Pres.tautologicalQuotient) ⟶
      (Modules.pullback Pres.localCoverHom).obj
        (Hom.conormalSheaf (Lift.identity π).baseChangeSection) :=
  Modules.restrictToSchemePreimage
    (Pres.chartRestrictConormalObjectIso.hom ≫
      Pres.localIdentityConormalMap ≫ Pres.chartConormalSheafIso.inv)

/-- The scheme atlas map on the covering, transported from pullback modules to étale
restriction along `localCoverHom`. -/
def tautologicalConormalRestrictHom :
    Modules.restrict (conormalObject Pres.tautologicalQuotient) Pres.localCoverHom ⟶
      Modules.restrict (Hom.conormalSheaf (Lift.identity π).baseChangeSection)
        Pres.localCoverHom :=
  (Modules.restrictFunctorIsoPullback Pres.localCoverHom).hom.app _ ≫
    Pres.localTautologicalPullbackHom ≫
      (Modules.restrictFunctorIsoPullback Pres.localCoverHom).inv.app _

/-- The tautological kernel-tensor-inverse on `P` compared with the conormal sheaf of the
diagonal section of `P ×_X P`, obtained by cover-dense extension of the scheme atlas map
along étale postcomposition with the local covering. -/
def tautologicalConormalToSheaf :
    conormalObject Pres.tautologicalQuotient ⟶
      Hom.conormalSheaf (Lift.identity π).baseChangeSection :=
  homOfUnderlying (structureSheaf P)
    ⟨Functor.IsCoverDense.sheafHom
      ((ToInternal.underlying (structureSheaf (ofOver Pres.localCoverOver))).map
        Pres.tautologicalConormalRestrictHom).hom⟩
    sorry sorry

/-- The tautological conormal comparison restricts to the scheme atlas map after the
constructed chart identifications. -/
theorem tautologicalConormalToSheaf_restrict :
    (Modules.restrictToScheme Pres.localCoverOver).map
          ((Modules.pullback Pres.localCoverHom).map Pres.tautologicalConormalToSheaf) ≫
        Pres.chartConormalSheafIso.hom =
      Pres.chartRestrictConormalObjectIso.hom ≫ Pres.localIdentityConormalMap := sorry

/-- The ambient comparison from a lift's base-changed bundle to the diagonal base change. -/
def liftToIdentityAmbientMap {T : AlgebraicSpace S} {f : T ⟶ X} (σ : Lift π f) :
    pullback π f ⟶ pullback π π :=
  eqToHom (congrArg (fun h ↦ pullback π h) σ.fac.symm) ≫
    precompAmbientMap (Lift.identity π) σ.hom

/-- The square relating a lift to the tautological diagonal section of the projective bundle. -/
theorem liftToIdentitySquare {T : AlgebraicSpace S} {f : T ⟶ X} (σ : Lift π f) :
    CommSq σ.hom σ.baseChangeSection (Lift.identity π).baseChangeSection
      (liftToIdentityAmbientMap σ) := sorry

/-- The source triangle of `liftSourceQuotient` commutes with pullback of the tautological
quotient. -/
theorem liftSourceQuotient_comm {T : AlgebraicSpace S} {f : T ⟶ X} (σ : Lift π f) :
    (Pres.liftSourceQuotient σ).hom ≫ (Iso.refl (Pres.liftSourceQuotient σ).object).hom =
      (Lift.pullbackSourceIso σ ℰ).symm.hom ≫
        (pullbackQuotient σ.hom Pres.tautologicalQuotient).hom := sorry

/-- The canonical comparison from the kernel-tensor-inverse of a lift's tautological quotient
to the conormal sheaf of the induced closed section. -/
def liftConormalToSheaf {T : AlgebraicSpace S} {f : T ⟶ X} (σ : Lift π f) :
    conormalObject (Pres.liftSourceQuotient σ) ⟶ Hom.conormalSheaf σ.baseChangeSection :=
  (conormalIsoOf (Pres.liftSourceQuotient σ)
      (pullbackQuotient σ.hom Pres.tautologicalQuotient)
      (Lift.pullbackSourceIso σ ℰ).symm (Iso.refl _)
      (Pres.liftSourceQuotient_comm σ)).hom ≫
    inv (pullbackConormalObjectComparison σ.hom Pres.tautologicalQuotient) ≫
    (Modules.pullback σ.hom).map Pres.tautologicalConormalToSheaf ≫
    Hom.Conormal.map (liftToIdentitySquare σ)

/-- The canonical conormal morphism attached to an explicit quotient representative
corresponding to a lift. -/
def liftConormalMap {T : AlgebraicSpace S} {f : T ⟶ X} (σ : Lift π f)
    (q : InvertibleQuotient ((Modules.pullback f).obj ℰ))
    (h : IsoClass.mk q = IsoClass.mk (Pres.liftSourceQuotient σ)) :
    conormalObject q ⟶ Hom.conormalSheaf σ.baseChangeSection :=
  (Pres.liftConormalRepresentativeIso σ q h).hom ≫ Pres.liftConormalToSheaf σ

/-- Precomposition of lifts gives the canonical square between their induced base-change
sections. -/
theorem precompConormalSquare {T R : AlgebraicSpace S} {f : T ⟶ X} (σ : Lift π f) (g : R ⟶ T) :
    CommSq g (σ.precomp g).baseChangeSection σ.baseChangeSection
      (precompAmbientMap σ g) :=
  ⟨(Lift.baseChangeSection_precomp σ g).symm⟩

/-- The canonical morphism of conormal sheaves associated to precomposition of lifts. -/
def precompConormalSheafMap {T R : AlgebraicSpace S} {f : T ⟶ X} (σ : Lift π f) (g : R ⟶ T) :
    (Modules.pullback g).obj (Hom.conormalSheaf σ.baseChangeSection) ⟶
      Hom.conormalSheaf (σ.precomp g).baseChangeSection :=
  Hom.Conormal.map (precompConormalSquare σ g)

/-- The pulled-back representative, transported to the source determined by the composite
base morphism. -/
def pullbackRepresentative {T R : AlgebraicSpace S} {f : T ⟶ X} (g : R ⟶ T)
    (q : InvertibleQuotient ((Modules.pullback f).obj ℰ)) :
    InvertibleQuotient ((Modules.pullback (g ≫ f)).obj ℰ) :=
  precomposeIso ((Modules.pullbackComp g f).app ℰ).symm (pullbackQuotient g q)

/-- The identity-pullback transport of a pulled-back representative commutes with the source
comparison. -/
theorem pullbackRepresentative_comm {T R : AlgebraicSpace S} {f : T ⟶ X} (g : R ⟶ T)
    (q : InvertibleQuotient ((Modules.pullback f).obj ℰ)) :
    (pullbackQuotient g q).hom ≫ (Iso.refl (pullbackQuotient g q).object).hom =
      ((Modules.pullbackComp g f).app ℰ).hom ≫ (pullbackRepresentative g q).hom := sorry

/-- Pulling back a representative corresponding to a lift gives a representative corresponding
to the precomposed lift. -/
theorem pullbackRepresentative_class {T R : AlgebraicSpace S} {f : T ⟶ X} (σ : Lift π f)
    (g : R ⟶ T) (q : InvertibleQuotient ((Modules.pullback f).obj ℰ))
    (h : IsoClass.mk q = IsoClass.mk (Pres.liftSourceQuotient σ)) :
    IsoClass.mk (pullbackRepresentative g q) =
      IsoClass.mk (Pres.liftSourceQuotient (σ.precomp g)) := sorry

/-- The source comparison for the conormal object of a representative under arbitrary
precomposition. -/
def liftConormalPullbackComparison {T R : AlgebraicSpace S} {f : T ⟶ X} (g : R ⟶ T)
    (q : InvertibleQuotient ((Modules.pullback f).obj ℰ)) :
    (Modules.pullback g).obj (conormalObject q) ⟶
      conormalObject (pullbackRepresentative g q) :=
  pullbackConormalObjectComparison g q ≫
    (conormalIsoOf (pullbackQuotient g q) (pullbackRepresentative g q)
      ((Modules.pullbackComp g f).app ℰ) (Iso.refl _)
      (pullbackRepresentative_comm g q)).hom

end SymmetricPresentation
end ProjectiveBundle
end AlgebraicSpace
end AlgebraicGeometry
