module

public import stacks_project.Chap108.Lemma_108_4_9_InternalHom
public import ReasLib.Algebra.Category.ModuleCat.Presheaf.Tensor.Bilinear
public import ReasLib.Algebra.Category.ModuleCat.Sheaf.RingedSite.SheafificationAdjunction
public import Mathlib.CategoryTheory.Monoidal.Closed.Basic

/-! Small-carrier tensor/Hom adjunction, with actual evaluation and currying data.
The constructions follow the repaired canonical InternalHom owner, retaining its tensor
and presheaf-bilinear owners; no adjoint or isomorphism is selected from an admitted existence. -/

@[expose] public section

open CategoryTheory CategoryTheory.MonoidalCategory Opposite AlgebraicGeometry
open AlgebraicGeometry.AlgebraicSpace AlgebraicGeometry.AlgebraicSpace.Modules
open SheafOfModules.RingedSite

noncomputable section

universe u

namespace AlgebraicGeometry.AlgebraicSpace.ModuleDerived.TensorPower.InternalHom

variable {S : Scheme.{u}} {X : AlgebraicSpace S}

-- Pin actual sheafification choice to the proved small-basis certificate.
-- Local instance justification (proof-local temporary data): Select the proved small-basis sheafification and local-bijection certificates in place of legacy admitted instances.
local instance certifiedWeakSheafify : HasWeakSheafify (smallEtaleTopology X) AddCommGrpCat.{u} :=
  (AlgebraicGeometry.AlgebraicSpace.ModuleDerived.TensorPower.Site.spaceHasSheafify X).isRightAdjoint

-- Local instance justification (proof-local temporary data): Select the proved small-basis sheafification and local-bijection certificates in place of legacy admitted instances.
local instance certifiedLocalBijections :
    (smallEtaleTopology X).WEqualsLocallyBijective AddCommGrpCat.{u} :=
  AlgebraicGeometry.AlgebraicSpace.ModuleDerived.TensorPower.Site.spaceWEquals X

abbrev Bilinear (F H G : commModules X) :=
  PresheafOfModules.BilinearMap (commStructureSheaf X).obj F.val H.val G.val

/-- The canonical sheafification tensor comparison, at the original coefficient universe. -/
def tensorIso (F H : commModules X) :
    F ⊗ H ≅ (moduleSheafification.{u + 1, u, u, u} (commStructureSheaf X)).obj
      (PresheafOfModules.Monoidal.tensorObj F.val H.val) :=
  (CategoryTheory.MonoidalCategory.tensorIso
    (moduleSheafificationValIso (commStructureSheaf X) F).symm
    (moduleSheafificationValIso (commStructureSheaf X) H).symm) ≪≫
      CategoryTheory.Functor.Monoidal.μIso
        (moduleSheafification.{u + 1, u, u, u} (commStructureSheaf X)) F.val H.val

/-- The existing presheaf tensor universal property followed by genuine module sheafification. -/
def tensorBilinearEquiv (F H G : commModules X) : (F ⊗ H ⟶ G) ≃ Bilinear F H G :=
  ((tensorIso F H).homCongr (Iso.refl G)).trans
    ((moduleSheafificationHomEquiv (commStructureSheaf X)
      (PresheafOfModules.Monoidal.tensorObj F.val H.val) G).trans
        PresheafOfModules.BilinearMap.homEquiv.symm)

/-- Currying evaluates the original bilinear map on the restricted fixed section. -/
def curryLocalApp {F H G : commModules X} (b : Bilinear F H G)
    (U : (smallEtaleSite X)ᵒᵖ) (y : H.val.obj U) (W : (Over U.unop)ᵒᵖ) :
    (F.over U.unop).val.obj W ⟶ (G.over U.unop).val.obj W :=
  ModuleCat.ofHom
    (X := (F.over U.unop).val.obj W) (Y := (G.over U.unop).val.obj W) {
    toFun := fun x ↦ b.app (op W.unop.left) x (H.val.map W.unop.hom.op y)
    map_add' := by sorry
    map_smul' := by sorry }

def curryLocal {F H G : commModules X} (b : Bilinear F H G)
    (U : (smallEtaleSite X)ᵒᵖ) (y : H.val.obj U) : Raw F G U where
  val := { app := curryLocalApp b U y, naturality := by sorry }

def curryApp {F H G : commModules X} (b : Bilinear F H G) (U : (smallEtaleSite X)ᵒᵖ) :
    H.val.obj U ⟶ (obj F G).val.obj U :=
  ModuleCat.ofHom (X := H.val.obj U) (Y := (obj F G).val.obj U) {
    toFun := fun y ↦ (decode F G U).symm (curryLocal b U y)
    map_add' := by sorry
    map_smul' := by sorry }

def curry {F H G : commModules X} (b : Bilinear F H G) : H ⟶ obj F G where
  val := { app := curryApp b, naturality := by sorry }

/-- Uncurrying evaluates the decoded local morphism at the terminal slice object. -/
def evalApp {F H G : commModules X} (f : H ⟶ obj F G) (U : (smallEtaleSite X)ᵒᵖ) :
    F.val.obj U →ₗ[(commStructureSheaf X).obj.obj U]
      H.val.obj U →ₗ[(commStructureSheaf X).obj.obj U] G.val.obj U where
  toFun x := {
    toFun := fun y ↦ ((decode F G U ((f.val.app U).hom y)).val.app (op (Over.mk (𝟙 U.unop)))).hom x
    map_add' := by sorry
    map_smul' := by sorry }
  map_add' := by sorry
  map_smul' := by sorry

def uncurry {F H G : commModules X} (f : H ⟶ obj F G) : Bilinear F H G where
  app := evalApp f
  naturality := by sorry

def bilinearEquiv (F H G : commModules X) : Bilinear F H G ≃ (H ⟶ obj F G) where
  toFun := curry
  invFun := uncurry
  left_inv := by sorry
  right_inv := by sorry

def homEquiv (F H G : commModules X) : (F ⊗ H ⟶ G) ≃ (H ⟶ obj F G) :=
  (tensorBilinearEquiv F H G).trans (bilinearEquiv F H G)

def adjunction (F : commModules X) : tensorLeft F ⊣ functor F :=
  Adjunction.mkOfHomEquiv {
    homEquiv := fun H G ↦ homEquiv F H G
    homEquiv_naturality_left_symm := by sorry
    homEquiv_naturality_right := by sorry }

@[implicit_reducible]
def closed (F : commModules X) : Closed F where
  rightAdj := functor F
  adj := adjunction F

@[instance_reducible]
def monoidalClosed (X : AlgebraicSpace S) : MonoidalClosed (commModules X) where
  closed := closed

/-- The encoded curry actually stores the local map with the expected section formula. -/
theorem curry_decode {F H G : commModules X} (b : Bilinear F H G)
    (U : (smallEtaleSite X)ᵒᵖ) (y : H.val.obj U) :
    decode F G U (((curry b).val.app U).hom y) = curryLocal b U y :=
  (decode F G U).apply_symm_apply _

/-- Every component of the local map is bilinear evaluation with actual restriction of y. -/
theorem curryLocal_apply {F H G : commModules X} (b : Bilinear F H G)
    (U : (smallEtaleSite X)ᵒᵖ) (y : H.val.obj U) (W : (Over U.unop)ᵒᵖ)
    (x : (F.over U.unop).val.obj W) :
    ((curryLocal b U y).val.app W).hom x =
      b.app (op W.unop.left) x (H.val.map W.unop.hom.op y) := rfl

end AlgebraicGeometry.AlgebraicSpace.ModuleDerived.TensorPower.InternalHom
