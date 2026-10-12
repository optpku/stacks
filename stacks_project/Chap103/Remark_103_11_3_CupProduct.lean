/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import Mathlib.CategoryTheory.Sites.CartesianMonoidal
public import Mathlib.LinearAlgebra.TensorProduct.Basic
public import ReasLib.Algebra.Category.ModuleCat.Presheaf.Tensor.Bilinear
public import ReasLib.Algebra.Category.ModuleCat.Sheaf.RingedSite.SheafificationAdjunction
public import ReasLib.Algebra.Category.ModuleCat.Sheaf.RingedSite.SheafificationMonoidal
public import ReasLib.Algebra.Category.ModuleCat.Sheaf.RingedSite.Tensor
public import stacks_project.Chap103.Proposition_103_11_1_DirectImage
public import stacks_project.Chap103.Remark_103_10_6_Tensor

/-!
# Degree-0 naive relative cup product along quasi-coherent direct image

The underived map `c : f_* F ⊗ f_* G ⟶ f_*(F ⊗ G)` is the degree-0 naive
relative cup product of a right adjoint, assembled on étale modules from the
type-valued product comparison of direct image and pure-tensor sections, then
lifted to `LQCoh^{fbc}`. Applying `Q` after the tensorator `μ` of
Remark 103.10.6 produces the quasi-coherent comparison.
-/

@[expose] public section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits
open CategoryTheory.MonoidalCategory CategoryTheory.CartesianMonoidalCategory
open CategoryTheory.ObjectProperty
open SheafOfModules SheafOfModules.RingedSite
open AlgebraicGeometry.GroupoidsOver
open scoped Bicategory TensorProduct

noncomputable section

universe u

namespace AlgebraicGeometry.GroupoidsOver

variable {S : Scheme.{u}}

/-- Sheafification of the pointwise étale tensor of two étale modules. -/
def etalePointwiseTensorSheafify {X : GroupoidsOver S} (F G : etaleModules X) :
    etaleModules X :=
  (moduleSheafification.{u + 1, u, u, u} (commEtaleStructureSheaf X)).obj
    (PresheafOfModules.Monoidal.tensorObj F.val G.val)

/-- Comparison from the sheafified pointwise étale tensor to `moduleTensorEtale`. -/
def etalePointwiseTensorSheafify_iso {X : GroupoidsOver S}
    (F G : etaleModules X) :
    etalePointwiseTensorSheafify F G ≅ moduleTensorEtale F G :=
  (Functor.Monoidal.μIso
      (moduleSheafification.{u + 1, u, u, u} (commEtaleStructureSheaf X))
      F.val G.val).symm ≪≫
    tensorIso
      (moduleSheafificationValIso.{u + 1, u, u, u}
        (commEtaleStructureSheaf X) F)
      (moduleSheafificationValIso.{u + 1, u, u, u}
        (commEtaleStructureSheaf X) G)

/-- Type-valued sheaf underlying an étale module. -/
def etaleModuleUnderlying {X : GroupoidsOver S} (F : etaleModules X) :
    Sheaf X.etaleTopology (Type u) :=
  (Sheaf.InternalModule.ToInternal.underlying (etaleStructureSheaf X)).obj F

/-- Pure tensor of étale sections, as a section of the étale module tensor. -/
def etaleTensorSection {X : GroupoidsOver S} {F G : etaleModules X}
    (U : X.totalᵒᵖ) (x : F.val.obj U) (y : G.val.obj U) :
    (moduleTensorEtale F G).val.obj U :=
  (etalePointwiseTensorSheafify_iso F G).hom.val.app U
    ((moduleSheafificationUnitToVal.{u + 1, u, u, u} (commEtaleStructureSheaf X)
        (PresheafOfModules.Monoidal.tensorObj F.val G.val)).app U (x ⊗ₜ y))

/-- Type-valued comparison `F_und ⊗ G_und ⟶ (F ⊗ G)_und` sending a pair of
sections to their pure tensor. -/
def etaleTensorSectionUnderlying {X : GroupoidsOver S} (F G : etaleModules X) :
    etaleModuleUnderlying F ⊗ etaleModuleUnderlying G ⟶
      etaleModuleUnderlying (moduleTensorEtale F G) where
  hom :=
    { app := fun U ↦
        TypeCat.ofHom fun p ↦
          etaleTensorSection U
            (((fst (etaleModuleUnderlying F) (etaleModuleUnderlying G)).hom.app U).hom p)
            (((snd (etaleModuleUnderlying F) (etaleModuleUnderlying G)).hom.app U).hom p)
      naturality := fun _ _ _ ↦ sorry }

/-- Canonical lax comparison `f_* P ⊗ f_* Q ⟶ f_*(P ⊗ Q)` of type-valued
direct image along `moduleDirectImageToposHom`. -/
def moduleDirectImage.typePushforward_prodLax {X Y : GroupoidsOver S}
    (f : X ⟶ Y) (P Q : Sheaf X.etaleTopology (Type u)) :
    ((moduleDirectImageToposHom f).toTopos.pushforward).obj P ⊗
      ((moduleDirectImageToposHom f).toTopos.pushforward).obj Q ⟶
      ((moduleDirectImageToposHom f).toTopos.pushforward).obj (P ⊗ Q) :=
  let φ := moduleDirectImageToposHom f
  (φ.toTopos.adjunction.homEquiv _ _)
    (prodComparison φ.toTopos.inverseImage
        (φ.toTopos.pushforward.obj P) (φ.toTopos.pushforward.obj Q) ≫
      (φ.toTopos.adjunction.counit.app P ⊗ₘ
        φ.toTopos.adjunction.counit.app Q))

/-- Type-valued degree-0 naive cup product
`(f_* F)_und ⊗ (f_* G)_und ⟶ (f_*(F ⊗ G))_und`. -/
def moduleDirectImage.naiveCupProductUnderlying {X Y : GroupoidsOver S}
    (f : X ⟶ Y) (F G : etaleModules X) :
    etaleModuleUnderlying ((moduleDirectImage f).obj F) ⊗
      etaleModuleUnderlying ((moduleDirectImage f).obj G) ⟶
      etaleModuleUnderlying ((moduleDirectImage f).obj (moduleTensorEtale F G)) :=
  let φ := moduleDirectImageToposHom f
  ((RingedSite.ToposHom.ModulePushforward.forgetIso φ).hom.app F ⊗ₘ
      (RingedSite.ToposHom.ModulePushforward.forgetIso φ).hom.app G) ≫
    moduleDirectImage.typePushforward_prodLax f
      (etaleModuleUnderlying F) (etaleModuleUnderlying G) ≫
      φ.toTopos.pushforward.map (etaleTensorSectionUnderlying F G) ≫
        (RingedSite.ToposHom.ModulePushforward.forgetIso φ).inv.app
          (moduleTensorEtale F G)

/-- Compatible bilinear map of étale sections representing the degree-0 naive
relative cup product. -/
def moduleDirectImage.naiveCupProductBilinear {X Y : GroupoidsOver S}
    (f : X ⟶ Y) (F G : etaleModules X) :
    PresheafOfModules.BilinearMap (commEtaleStructureSheaf Y).obj
      ((moduleDirectImage f).obj F).val ((moduleDirectImage f).obj G).val
      ((moduleDirectImage f).obj (moduleTensorEtale F G)).val where
  app U :=
    LinearMap.mk₂ ((commEtaleStructureSheaf Y).obj.obj U)
      (fun x y ↦
        (moduleDirectImage.naiveCupProductUnderlying f F G).hom.app U (x, y))
      sorry sorry sorry sorry
  naturality := sorry

/-- Étale-level degree-0 naive relative cup product
`c : f_* F ⊗ f_* G ⟶ f_*(F ⊗ G)`. -/
def moduleDirectImage.naiveCupProduct {X Y : GroupoidsOver S}
    (f : X ⟶ Y) (F G : etaleModules X) :
    moduleTensorEtale ((moduleDirectImage f).obj F)
      ((moduleDirectImage f).obj G) ⟶
      (moduleDirectImage f).obj (moduleTensorEtale F G) :=
  (etalePointwiseTensorSheafify_iso
      ((moduleDirectImage f).obj F) ((moduleDirectImage f).obj G)).inv ≫
    (moduleSheafificationHomEquiv.{u + 1, u, u, u}
        (commEtaleStructureSheaf Y)
        (PresheafOfModules.Monoidal.tensorObj
          ((moduleDirectImage f).obj F).val
          ((moduleDirectImage f).obj G).val)
        ((moduleDirectImage f).obj (moduleTensorEtale F G))).symm
      (PresheafOfModules.BilinearMap.toHom
        (moduleDirectImage.naiveCupProductBilinear f F G))

/-- `naiveCupProduct` is descent of the sectionwise bilinear cup product along
the sheafified pointwise tensor. -/
theorem moduleDirectImage.naiveCupProduct_eq {X Y : GroupoidsOver S}
    (f : X ⟶ Y) (F G : etaleModules X) :
    moduleDirectImage.naiveCupProduct f F G =
      (etalePointwiseTensorSheafify_iso
          ((moduleDirectImage f).obj F) ((moduleDirectImage f).obj G)).inv ≫
        (moduleSheafificationHomEquiv.{u + 1, u, u, u}
            (commEtaleStructureSheaf Y)
            (PresheafOfModules.Monoidal.tensorObj
              ((moduleDirectImage f).obj F).val
              ((moduleDirectImage f).obj G).val)
            ((moduleDirectImage f).obj (moduleTensorEtale F G))).symm
          (PresheafOfModules.BilinearMap.toHom
            (moduleDirectImage.naiveCupProductBilinear f F G)) :=
  rfl

/-- Naturality of the étale naive cup product in both module arguments. -/
theorem moduleDirectImage.naiveCupProduct_natural {X Y : GroupoidsOver S}
    (f : X ⟶ Y) {F F' G G' : etaleModules X} (α : F ⟶ F') (β : G ⟶ G') :
    moduleTensorMap.{u + 1, u, u}
        ((moduleDirectImage f).map α) ((moduleDirectImage f).map β) ≫
      moduleDirectImage.naiveCupProduct f F' G' =
    moduleDirectImage.naiveCupProduct f F G ≫
      (moduleDirectImage f).map (moduleTensorMap.{u + 1, u, u} α β) :=
  sorry

/-- Tensor product of morphisms of quasi-coherent modules. -/
def QCoh.tensorHom {X : GroupoidsOver S} [AlgebraicStack X]
    {F₁ F₂ G₁ G₂ : QCoh X} (α : F₁ ⟶ F₂) (β : G₁ ⟶ G₂) :
    QCoh.tensor F₁ G₁ ⟶ QCoh.tensor F₂ G₂ :=
  ObjectProperty.homMk
    ((fromCommFppfModules X).map
      (moduleTensorMap.{u + 1, u, u}
        ((toCommFppfModules X).map α.hom)
        ((toCommFppfModules X).map β.hom)))

/-- The underlying fppf morphism of `QCoh.tensorHom` is the transported module
tensor map. -/
theorem QCoh.tensorHom_hom {X : GroupoidsOver S} [AlgebraicStack X]
    {F₁ F₂ G₁ G₂ : QCoh X} (α : F₁ ⟶ F₂) (β : G₁ ⟶ G₂) :
    (QCoh.tensorHom α β).hom =
      (fromCommFppfModules X).map
        (moduleTensorMap.{u + 1, u, u}
          ((toCommFppfModules X).map α.hom)
          ((toCommFppfModules X).map β.hom)) :=
  rfl

namespace LQCohFbc

/-- Degree-0 naive relative cup product in `LQCoh^{fbc}(𝒪_Y)`:
`c : f_* F ⊗ f_* G ⟶ f_*(F ⊗ G)`, with source and target in `LQCoh^{fbc}`. -/
def naiveRelativeCupProduct {X Y : GroupoidsOver S}
    [AlgebraicStack X] [AlgebraicStack Y] (f : X ⟶ Y)
    [AlgebraicStack.QuasiCompact f] [AlgebraicStack.QuasiSeparated f]
    (F G : QCoh X) :
    ofModuleTensorEtale
        ((directImage f).obj ((QCoh.toLQCohFbc X).obj F))
        ((directImage f).obj ((QCoh.toLQCohFbc X).obj G)) ⟶
      (directImage f).obj ((QCoh.toLQCohFbc X).obj (QCoh.tensor F G)) :=
  ObjectProperty.homMk
    (moduleDirectImage.naiveCupProduct f
        ((inclusion X).obj ((QCoh.toLQCohFbc X).obj F))
        ((inclusion X).obj ((QCoh.toLQCohFbc X).obj G)) ≫
      (moduleDirectImage f).map (QCoh.toLQCohFbc_tensorator_hom F G))

/-- The underlying étale morphism of `naiveRelativeCupProduct` is the étale
cup product followed by direct image of the inclusion tensorator. -/
theorem naiveRelativeCupProduct_hom {X Y : GroupoidsOver S}
    [AlgebraicStack X] [AlgebraicStack Y] (f : X ⟶ Y)
    [AlgebraicStack.QuasiCompact f] [AlgebraicStack.QuasiSeparated f]
    (F G : QCoh X) :
    (naiveRelativeCupProduct f F G).hom =
      moduleDirectImage.naiveCupProduct f
          ((inclusion X).obj ((QCoh.toLQCohFbc X).obj F))
          ((inclusion X).obj ((QCoh.toLQCohFbc X).obj G)) ≫
        (moduleDirectImage f).map (QCoh.toLQCohFbc_tensorator_hom F G) :=
  rfl

/-- Top horizontal of the Remark 103.11.3 square: the tensor of the two
adjunction counits. -/
def directImageTensorCounit {X Y : GroupoidsOver S}
    [AlgebraicStack X] [AlgebraicStack Y] (f : X ⟶ Y)
    [AlgebraicStack.QuasiCompact f] [AlgebraicStack.QuasiSeparated f]
    (adj : QCoh.toLQCohFbc Y ⊣ toQCoh Y) (F G : QCoh X) :
    ofModuleTensorEtale
        ((QCoh.toLQCohFbc Y).obj ((QCoh.directImage f).obj F))
        ((QCoh.toLQCohFbc Y).obj ((QCoh.directImage f).obj G)) ⟶
      ofModuleTensorEtale
        ((directImage f).obj ((QCoh.toLQCohFbc X).obj F))
        ((directImage f).obj ((QCoh.toLQCohFbc X).obj G)) :=
  tensorCounit adj
    ((directImage f).obj ((QCoh.toLQCohFbc X).obj F))
    ((directImage f).obj ((QCoh.toLQCohFbc X).obj G))

/-- `directImageTensorCounit` is the tensor of the two counit components. -/
theorem directImageTensorCounit_eq {X Y : GroupoidsOver S}
    [AlgebraicStack X] [AlgebraicStack Y] (f : X ⟶ Y)
    [AlgebraicStack.QuasiCompact f] [AlgebraicStack.QuasiSeparated f]
    (adj : QCoh.toLQCohFbc Y ⊣ toQCoh Y) (F G : QCoh X) :
    directImageTensorCounit f adj F G =
      tensorHom
        (adj.counit.app ((directImage f).obj ((QCoh.toLQCohFbc X).obj F)))
        (adj.counit.app ((directImage f).obj ((QCoh.toLQCohFbc X).obj G))) :=
  rfl

/-- Naturality of the `LQCoh^{fbc}` naive cup product in both quasi-coherent
arguments. -/
theorem naiveRelativeCupProduct_natural {X Y : GroupoidsOver S}
    [AlgebraicStack X] [AlgebraicStack Y] (f : X ⟶ Y)
    [AlgebraicStack.QuasiCompact f] [AlgebraicStack.QuasiSeparated f]
    {F F' G G' : QCoh X} (α : F ⟶ F') (β : G ⟶ G') :
    tensorHom
        ((directImage f).map ((QCoh.toLQCohFbc X).map α))
        ((directImage f).map ((QCoh.toLQCohFbc X).map β)) ≫
      naiveRelativeCupProduct f F' G' =
    naiveRelativeCupProduct f F G ≫
      (directImage f).map ((QCoh.toLQCohFbc X).map (QCoh.tensorHom α β)) :=
  sorry

end LQCohFbc

namespace QCoh

/-- Left vertical of the Remark 103.11.3 square: `Q(c)` after the tensorator
`μ` of `Q`. -/
def directImage_tensorComparison {X Y : GroupoidsOver S}
    [AlgebraicStack X] [AlgebraicStack Y] (f : X ⟶ Y)
    [AlgebraicStack.QuasiCompact f] [AlgebraicStack.QuasiSeparated f]
    (adj : toLQCohFbc Y ⊣ LQCohFbc.toQCoh Y) (F G : QCoh X) :
    tensor ((directImage f).obj F) ((directImage f).obj G) ⟶
      (directImage f).obj (tensor F G) :=
  LQCohFbc.toQCoh_μ adj
      ((LQCohFbc.directImage f).obj ((toLQCohFbc X).obj F))
      ((LQCohFbc.directImage f).obj ((toLQCohFbc X).obj G)) ≫
    (LQCohFbc.toQCoh Y).map (LQCohFbc.naiveRelativeCupProduct f F G)

/-- `directImage_tensorComparison` is `μ` followed by `Q(c)`. -/
theorem directImage_tensorComparison_eq {X Y : GroupoidsOver S}
    [AlgebraicStack X] [AlgebraicStack Y] (f : X ⟶ Y)
    [AlgebraicStack.QuasiCompact f] [AlgebraicStack.QuasiSeparated f]
    (adj : toLQCohFbc Y ⊣ LQCohFbc.toQCoh Y) (F G : QCoh X) :
    directImage_tensorComparison f adj F G =
      LQCohFbc.toQCoh_μ adj
          ((LQCohFbc.directImage f).obj ((toLQCohFbc X).obj F))
          ((LQCohFbc.directImage f).obj ((toLQCohFbc X).obj G)) ≫
        (LQCohFbc.toQCoh Y).map (LQCohFbc.naiveRelativeCupProduct f F G) :=
  rfl

/-- Left vertical of the Remark 103.11.3 square, after including into
`LQCoh^{fbc}` along the étale tensorator of `toLQCohFbc`. -/
def directImage_tensorComparison_included {X Y : GroupoidsOver S}
    [AlgebraicStack X] [AlgebraicStack Y] (f : X ⟶ Y)
    [AlgebraicStack.QuasiCompact f] [AlgebraicStack.QuasiSeparated f]
    (adj : toLQCohFbc Y ⊣ LQCohFbc.toQCoh Y) (F G : QCoh X) :
    LQCohFbc.ofModuleTensorEtale
        ((toLQCohFbc Y).obj ((directImage f).obj F))
        ((toLQCohFbc Y).obj ((directImage f).obj G)) ⟶
      (toLQCohFbc Y).obj ((directImage f).obj (tensor F G)) :=
  toLQCohFbc_tensorator ((directImage f).obj F) ((directImage f).obj G) ≫
    (toLQCohFbc Y).map (directImage_tensorComparison f adj F G)

/-- `directImage_tensorComparison_included` is the inclusion tensorator
followed by `i(Q(c))`. -/
theorem directImage_tensorComparison_included_eq {X Y : GroupoidsOver S}
    [AlgebraicStack X] [AlgebraicStack Y] (f : X ⟶ Y)
    [AlgebraicStack.QuasiCompact f] [AlgebraicStack.QuasiSeparated f]
    (adj : toLQCohFbc Y ⊣ LQCohFbc.toQCoh Y) (F G : QCoh X) :
    directImage_tensorComparison_included f adj F G =
      toLQCohFbc_tensorator ((directImage f).obj F) ((directImage f).obj G) ≫
        (toLQCohFbc Y).map (directImage_tensorComparison f adj F G) :=
  rfl

end QCoh

end AlgebraicGeometry.GroupoidsOver
