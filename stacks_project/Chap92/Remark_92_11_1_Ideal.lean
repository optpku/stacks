/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import Mathlib.Algebra.Category.Grp.Basic
public import Mathlib.RingTheory.Ideal.Cotangent
public import Mathlib.RingTheory.TensorProduct.Basic
public import stacks_project.Chap92.Lemma_92_7_1_Omega

/-!
# Kernel and conormal sheaves on the polynomial site

This leaf owns the abelian sheaf `𝒥 = Ker(O ⟶ underline{B})` and the
`underline{B}`-module sheaf `𝒥/𝒥²` on `C_{B/A}`, together with the sheaf map
`𝒥/𝒥² ⟶ Ω_{O/A} ⊗_O underline{B}`.
-/

@[expose] public section

open CategoryTheory Opposite
open scoped TensorProduct

noncomputable section

universe u

namespace CommAlgCat.Over.Polynomial.Site

variable {A B : Type u} [CommRing A] [CommRing B] [Algebra A B]

/-- The kernel of a polynomial arrow `P ⟶ B`, as an abelian group. -/
def kernelObj (X : Algebra.PolynomialOver A B) : AddCommGrpCat.{u} :=
  AddCommGrpCat.of (RingHom.ker X.obj.hom.hom.toRingHom)

/-- Unfolding `kernelObj` recovers the unbundled kernel of `P ⟶ B`. -/
theorem kernelObj_eq (X : Algebra.PolynomialOver A B) :
    kernelObj X = AddCommGrpCat.of (RingHom.ker X.obj.hom.hom.toRingHom) :=
  sorry

/-- A morphism of polynomial arrows sends `Ker(P ⟶ B)` into `Ker(P' ⟶ B)`. -/
theorem kernel_le_comap {X Y : Algebra.PolynomialOver A B} (f : X ⟶ Y) :
    RingHom.ker X.obj.hom.hom.toRingHom ≤
      (RingHom.ker Y.obj.hom.hom.toRingHom).comap f.hom.left.hom.toRingHom :=
  sorry

/-- The map on kernels induced by a morphism of polynomial arrows over `B`. -/
def kernelMap {X Y : Algebra.PolynomialOver A B} (f : X ⟶ Y) :
    kernelObj X ⟶ kernelObj Y :=
  AddCommGrpCat.ofHom
    { toFun := fun j ↦
        ⟨f.hom.left.hom.toRingHom (j : X.obj.left), kernel_le_comap f j.2⟩
      map_zero' := sorry
      map_add' := sorry }

/-- Identity morphisms act as the identity on kernels. -/
theorem kernelMap_id (X : Algebra.PolynomialOver A B) :
    kernelMap (𝟙 X) = 𝟙 (kernelObj X) :=
  sorry

/-- Composition of polynomial-arrow morphisms maps to composition of kernel maps. -/
theorem kernelMap_comp {X Y Z : Algebra.PolynomialOver A B} (f : X ⟶ Y) (g : Y ⟶ Z) :
    kernelMap (f ≫ g) = kernelMap f ≫ kernelMap g :=
  sorry

variable (A B) in
/-- The covariant functor of kernels on polynomial arrows `P ⟶ B`. -/
def kernelCov : Algebra.PolynomialOver A B ⥤ AddCommGrpCat.{u} where
  obj := kernelObj
  map f := kernelMap f
  map_id X := kernelMap_id X
  map_comp f g := kernelMap_comp f g

/-- Objects of `kernelCov` are the kernels of the corresponding polynomial arrows. -/
theorem kernelCov_obj (X : Algebra.PolynomialOver A B) :
    (kernelCov A B).obj X = kernelObj X :=
  sorry

variable (A B) in
/-- The abelian sheaf `𝒥 = Ker(O ⟶ underline{B})` on `C_{B/A}`. -/
def kernelPresheaf : (Algebra.PolynomialSite A B)ᵒᵖ ⥤ AddCommGrpCat.{u} :=
  unopUnop (Algebra.PolynomialOver A B) ⋙ kernelCov A B

/-- Evaluating `kernelPresheaf` on a double-opposite polynomial arrow recovers `kernelObj`. -/
theorem kernelPresheaf_obj (X : (Algebra.PolynomialSite A B)ᵒᵖ) :
    (kernelPresheaf A B).obj X = kernelObj (unop (unop X)) :=
  sorry

/-- `kernelPresheaf` is precomposition of `kernelCov` with the double-opposite equivalence. -/
theorem kernelPresheaf_eq :
    kernelPresheaf A B = unopUnop (Algebra.PolynomialOver A B) ⋙ kernelCov A B :=
  sorry

/-- Components of `kernelPresheaf` on morphisms are `kernelMap` of the underlying polynomial
arrow. -/
theorem kernelPresheaf_map {X Y : (Algebra.PolynomialSite A B)ᵒᵖ} (f : X ⟶ Y) :
    (kernelPresheaf A B).map f = kernelMap f.unop.unop :=
  sorry

/-- The conormal module `J/J² ⊗_P B` of a polynomial arrow `P ⟶ B`, in the presence of the
induced `P`-algebra structure on `B`. -/
def conormalObjWith (X : Algebra.PolynomialOver A B) [Algebra X.obj.left B] :
    ModuleCat.{u} B :=
  ModuleCat.of B (B ⊗[X.obj.left] (RingHom.ker (algebraMap X.obj.left B)).Cotangent)

/-- The conormal module `J/J² ⊗_P B` of a polynomial arrow `P ⟶ B`. -/
def conormalObj (X : Algebra.PolynomialOver A B) : ModuleCat.{u} B :=
  @conormalObjWith A B _ _ _ X (algebraToBase X)

/-- Unfolding `conormalObj` recovers the unbundled base change of `J/J²`. -/
theorem conormalObj_eq (X : Algebra.PolynomialOver A B) :
    conormalObj X = @conormalObjWith A B _ _ _ X (algebraToBase X) :=
  sorry

/-- A morphism of polynomial arrows sends `Ker(P ⟶ B)` into `Ker(P' ⟶ B)`, in the presence
of the induced algebra structures. -/
theorem kernel_le_comapWith {X Y : Algebra.PolynomialOver A B} (f : X ⟶ Y)
    [Algebra X.obj.left B] [Algebra Y.obj.left B] [Algebra X.obj.left Y.obj.left] :
    RingHom.ker (algebraMap X.obj.left B) ≤
      (RingHom.ker (algebraMap Y.obj.left B)).comap (algebraMap X.obj.left Y.obj.left) :=
  sorry

/-- The map on conormal modules induced by a morphism of polynomial arrows, in the presence
of the induced algebra structures. -/
def conormalMapWith {X Y : Algebra.PolynomialOver A B} (f : X ⟶ Y)
    [Algebra X.obj.left B] [Algebra Y.obj.left B]
    [Algebra X.obj.left Y.obj.left]
    [IsScalarTower A X.obj.left Y.obj.left]
    [IsScalarTower X.obj.left Y.obj.left B] :
    conormalObjWith X ⟶ conormalObjWith Y :=
  ModuleCat.ofHom
    (((Ideal.mapCotangent
          (RingHom.ker (algebraMap X.obj.left B))
          (RingHom.ker (algebraMap Y.obj.left B))
          (Algebra.ofId X.obj.left Y.obj.left)
          (kernel_le_comapWith f)).liftBaseChange Y.obj.left).baseChange B ∘ₗ
      (TensorProduct.AlgebraTensorModule.cancelBaseChange
        X.obj.left Y.obj.left B B
        (RingHom.ker (algebraMap X.obj.left B)).Cotangent).symm.toLinearMap)

/-- The map on conormal modules induced by a morphism of polynomial arrows over `B`. -/
def conormalMap {X Y : Algebra.PolynomialOver A B} (f : X ⟶ Y) :
    conormalObj X ⟶ conormalObj Y :=
  @conormalMapWith A B _ _ _ X Y f (algebraToBase X) (algebraToBase Y) (algebraOfHom f)
    (@isScalarTower_algebraOfHom A B _ _ _ X Y f (algebraOfHom f))
    (@isScalarTower_toBase A B _ _ _ X Y f (algebraOfHom f) (algebraToBase Y) (algebraToBase X))

/-- Unfolding `conormalMap` recovers the base-changed `Ideal.mapCotangent`. -/
theorem conormalMap_eq {X Y : Algebra.PolynomialOver A B} (f : X ⟶ Y) :
    conormalMap f =
      @conormalMapWith A B _ _ _ X Y f (algebraToBase X) (algebraToBase Y) (algebraOfHom f)
        (@isScalarTower_algebraOfHom A B _ _ _ X Y f (algebraOfHom f))
        (@isScalarTower_toBase A B _ _ _ X Y f (algebraOfHom f) (algebraToBase Y)
          (algebraToBase X)) :=
  sorry

/-- Identity morphisms act as the identity on conormal modules. -/
theorem conormalMap_id (X : Algebra.PolynomialOver A B) :
    conormalMap (𝟙 X) = 𝟙 (conormalObj X) :=
  sorry

/-- Composition of polynomial-arrow morphisms maps to composition of conormal maps. -/
theorem conormalMap_comp {X Y Z : Algebra.PolynomialOver A B} (f : X ⟶ Y) (g : Y ⟶ Z) :
    conormalMap (f ≫ g) = conormalMap f ≫ conormalMap g :=
  sorry

variable (A B) in
/-- The covariant functor of conormal modules on polynomial arrows `P ⟶ B`. -/
def conormalCov : Algebra.PolynomialOver A B ⥤ ModuleCat.{u} B where
  obj := conormalObj
  map f := conormalMap f
  map_id X := conormalMap_id X
  map_comp f g := conormalMap_comp f g

/-- Objects of `conormalCov` are the conormal modules of the corresponding polynomial
arrow. -/
theorem conormalCov_obj (X : Algebra.PolynomialOver A B) :
    (conormalCov A B).obj X = conormalObj X :=
  sorry

variable (A B) in
/-- The sheaf `𝒥/𝒥²` on `C_{B/A}`, as a functor `(PolynomialSite A B)ᵒᵖ ⥤ ModuleCat B`. -/
def conormalSheaf : (Algebra.PolynomialSite A B)ᵒᵖ ⥤ ModuleCat.{u} B :=
  unopUnop (Algebra.PolynomialOver A B) ⋙ conormalCov A B

/-- Evaluating `conormalSheaf` on a double-opposite polynomial arrow recovers `conormalObj`. -/
theorem conormalSheaf_obj (X : (Algebra.PolynomialSite A B)ᵒᵖ) :
    (conormalSheaf A B).obj X = conormalObj (unop (unop X)) :=
  sorry

/-- `conormalSheaf` is precomposition of `conormalCov` with the double-opposite equivalence. -/
theorem conormalSheaf_eq :
    conormalSheaf A B = unopUnop (Algebra.PolynomialOver A B) ⋙ conormalCov A B :=
  sorry

/-- Components of `conormalSheaf` on morphisms are `conormalMap` of the underlying polynomial
arrow. -/
theorem conormalSheaf_map {X Y : (Algebra.PolynomialSite A B)ᵒᵖ} (f : X ⟶ Y) :
    (conormalSheaf A B).map f = conormalMap f.unop.unop :=
  sorry

/-- The naive differential `J/J² ⊗_P B ⟶ Ω[P ⁄ A] ⊗[P] B` of a polynomial arrow, in the
presence of the induced `P`-algebra structure on `B`. -/
def conormalToOmegaAppWith (X : Algebra.PolynomialOver A B) [Algebra X.obj.left B] :
    conormalObjWith X ⟶ omegaSheafObjWith X :=
  ModuleCat.ofHom
    ((KaehlerDifferential.kerCotangentToTensor A X.obj.left B).liftBaseChange B)

/-- The naive differential `J/J² ⊗_P B ⟶ Ω[P ⁄ A] ⊗[P] B` of a polynomial arrow. -/
def conormalToOmegaApp (X : Algebra.PolynomialOver A B) :
    conormalObj X ⟶ omegaSheafObj X :=
  @conormalToOmegaAppWith A B _ _ _ X (algebraToBase X)

/-- Unfolding `conormalToOmegaApp` recovers the base change of
`KaehlerDifferential.kerCotangentToTensor`. -/
theorem conormalToOmegaApp_eq (X : Algebra.PolynomialOver A B) :
    conormalToOmegaApp X = @conormalToOmegaAppWith A B _ _ _ X (algebraToBase X) :=
  sorry

variable (A B) in
/-- The sheaf map `𝒥/𝒥² ⟶ Ω_{O/A} ⊗_O underline{B}` on `C_{B/A}`. -/
def conormalToOmega : conormalSheaf A B ⟶ omegaSheaf A B where
  app X := conormalToOmegaApp (unop (unop X))
  naturality := fun _ _ _ ↦ sorry

/-- Components of `conormalToOmega` are the objectwise naive differentials. -/
theorem conormalToOmega_app (X : (Algebra.PolynomialSite A B)ᵒᵖ) :
    (conormalToOmega A B).app X = conormalToOmegaApp (unop (unop X)) :=
  sorry

end CommAlgCat.Over.Polynomial.Site
