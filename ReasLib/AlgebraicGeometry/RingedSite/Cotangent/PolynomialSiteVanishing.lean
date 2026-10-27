/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import Mathlib.Algebra.Category.Grp.Basic
public import Mathlib.RingTheory.Ideal.Cotangent
public import Mathlib.RingTheory.TensorProduct.Basic
public import ReasLib.RingTheory.CotangentComplex.AbelianComparison
import Mathlib.Tactic.CrossRefAttribute

/-!
# Kernel and conormal sheaves on the polynomial site

The kernel presheaf is the abelian presheaf `𝒥 = Ker(O ⟶ underline{B})` and the
`underline{B}`-module sheaf `𝒥/𝒥²` on the polynomial presentation site, together with the presheaf map
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
      map_zero' := by
        apply Subtype.ext
        exact map_zero _
      map_add' := by
        intro x y
        apply Subtype.ext
        exact map_add _ _ _ }

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
    [Algebra X.obj.left B] [Algebra Y.obj.left B] [Algebra X.obj.left Y.obj.left]
    [IsScalarTower X.obj.left Y.obj.left B] :
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
    (algebraOfHom_isScalarTower f)
    (toBase_isScalarTower f)

/-- Unfolding `conormalMap` recovers the base-changed `Ideal.mapCotangent`. -/
theorem conormalMap_eq {X Y : Algebra.PolynomialOver A B} (f : X ⟶ Y) :
    conormalMap f =
      @conormalMapWith A B _ _ _ X Y f (algebraToBase X) (algebraToBase Y) (algebraOfHom f)
        (algebraOfHom_isScalarTower f)
        (toBase_isScalarTower f) :=
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
  naturality := by
    intro X Y f
    let f' := (unopUnop (Algebra.PolynomialOver A B)).map f
    -- Local instance justification (proof-local temporary data): The augmentation of the source polynomial arrow to `B` induces this algebra structure, needed to form its conormal tensor product in the naturality equation.
    letI : Algebra ((unopUnop (Algebra.PolynomialOver A B)).obj X).obj.left B :=
      algebraToBase ((unopUnop (Algebra.PolynomialOver A B)).obj X)
    -- Local instance justification (proof-local temporary data): The augmentation of the target polynomial arrow to `B` induces this algebra structure, needed to form its conormal tensor product in the naturality equation.
    letI : Algebra ((unopUnop (Algebra.PolynomialOver A B)).obj Y).obj.left B :=
      algebraToBase ((unopUnop (Algebra.PolynomialOver A B)).obj Y)
    -- Local instance justification (proof-local temporary data): The polynomial-site morphism `f'` induces this algebra structure, needed for the induced map between the source and target conormal modules.
    letI : Algebra ((unopUnop (Algebra.PolynomialOver A B)).obj X).obj.left
        ((unopUnop (Algebra.PolynomialOver A B)).obj Y).obj.left := algebraOfHom f'
    -- Local instance justification (proof-local temporary data): The morphism-induced algebra structure supplies this scalar tower, needed to compare tensor products over the source and target polynomial rings.
    letI : IsScalarTower A ((unopUnop (Algebra.PolynomialOver A B)).obj X).obj.left
        ((unopUnop (Algebra.PolynomialOver A B)).obj Y).obj.left := algebraOfHom_isScalarTower f'
    -- Local instance justification (proof-local temporary data): The compatible augmentations along `f'` supply this scalar tower, needed for naturality of the conormal-to-differentials map after base change to `B`.
    letI : IsScalarTower ((unopUnop (Algebra.PolynomialOver A B)).obj X).obj.left
        ((unopUnop (Algebra.PolynomialOver A B)).obj Y).obj.left B := toBase_isScalarTower f'
    apply ModuleCat.hom_ext
    apply LinearMap.ext
    intro z
    change (conormalToOmegaApp ((unopUnop (Algebra.PolynomialOver A B)).obj Y))
        (conormalMap f' z) =
      (omegaSheafMap f')
        (conormalToOmegaApp ((unopUnop (Algebra.PolynomialOver A B)).obj X) z)
    induction z using TensorProduct.induction_on with
    | zero =>
        change (conormalToOmegaApp ((unopUnop (Algebra.PolynomialOver A B)).obj Y)).hom
            ((conormalMap f').hom 0) =
          (omegaSheafMap f').hom
            ((conormalToOmegaApp ((unopUnop (Algebra.PolynomialOver A B)).obj X)).hom 0)
        rw [(conormalMap f').hom.map_zero,
          (conormalToOmegaApp ((unopUnop (Algebra.PolynomialOver A B)).obj Y)).hom.map_zero,
          (conormalToOmegaApp ((unopUnop (Algebra.PolynomialOver A B)).obj X)).hom.map_zero,
          (omegaSheafMap f').hom.map_zero]
    | add x y hx hy =>
        let x' : (conormalObj ((unopUnop (Algebra.PolynomialOver A B)).obj X)) := x
        let y' : (conormalObj ((unopUnop (Algebra.PolynomialOver A B)).obj X)) := y
        change (conormalToOmegaApp ((unopUnop (Algebra.PolynomialOver A B)).obj Y)).hom
            ((conormalMap f').hom (x' + y')) =
          (omegaSheafMap f').hom
            ((conormalToOmegaApp ((unopUnop (Algebra.PolynomialOver A B)).obj X)).hom (x' + y'))
        have hmap := (conormalMap f').hom.map_add x' y'
        rw [hmap,
          (conormalToOmegaApp ((unopUnop (Algebra.PolynomialOver A B)).obj Y)).hom.map_add,
          (conormalToOmegaApp ((unopUnop (Algebra.PolynomialOver A B)).obj X)).hom.map_add,
          (omegaSheafMap f').hom.map_add, hx, hy]
    | tmul b j =>
        obtain ⟨j, rfl⟩ := Ideal.toCotangent_surjective _ j
        dsimp only [conormalSheaf, omegaSheaf, conormalCov, omegaSheafCov,
          conormalToOmegaApp, conormalToOmegaAppWith, conormalMap,
          conormalMapWith, omegaSheafMap, omegaSheafObj, conormalObj,
          omegaSheafObjWith, conormalObjWith, omegaSheafMapWith]
        change
          (LinearMap.liftBaseChange B _)
              ((LinearMap.baseChange B _)
                ((TensorProduct.AlgebraTensorModule.cancelBaseChange _ _ _ _ _).symm
                  (b ⊗ₜ (Ideal.toCotangent _ j)))) =
            (KaehlerDifferential.tensorMapBaseChange A _ _ B)
              ((LinearMap.liftBaseChange B _)
                (b ⊗ₜ (Ideal.toCotangent _ j)))
        simp [KaehlerDifferential.tensorMapBaseChange_tmul,
          KaehlerDifferential.map_D,
          TensorProduct.AlgebraTensorModule.cancelBaseChange_symm_tmul,
          LinearMap.liftBaseChange_tmul, LinearMap.baseChange_tmul,
          KaehlerDifferential.kerCotangentToTensor_toCotangent,
          Ideal.mapCotangent_toCotangent]

/-- Components of `conormalToOmega` are the objectwise naive differentials. -/
theorem conormalToOmega_app (X : (Algebra.PolynomialSite A B)ᵒᵖ) :
    (conormalToOmega A B).app X = conormalToOmegaApp (unop (unop X)) :=
  sorry

end CommAlgCat.Over.Polynomial.Site

open CategoryTheory.Limits Algebra Algebra.PolynomialSite
open CommAlgCat.Over.Polynomial.Site
open scoped CategoryTheory

universe q q'

namespace Algebra.PolynomialSite

variable (A B : Type u) [CommRing A] [CommRing B] [Algebra A B]

section AbelianGroups

variable [HasColimitsOfShape (PolynomialSite A B)ᵒᵖ AddCommGrpCat.{u}]
variable [HasDerivedCategory.{q'} AddCommGrpCat.{u}]
variable [HasDerivedCategory.{q} ((PolynomialSite A B)ᵒᵖ ⥤ AddCommGrpCat.{u})]
variable [Functor.HasLeftDerivedFunctor
  (categoryOverPointColimitToDerived (PolynomialSite A B) AddCommGrpCat.{u})
  (HomotopyCategory.quasiIso ((PolynomialSite A B)ᵒᵖ ⥤ AddCommGrpCat.{u})
    (ComplexShape.up ℤ))]

/-- The derived lower shriek of the kernel presheaf on the polynomial presentation site vanishes. -/
@[stacks 08R7]
theorem lowerShriek_kernel_isZero :
    IsZero
      ((Lπ![(PolynomialSite A B), AddCommGrpCat.{u}]).obj
        ((DerivedCategory.singleFunctor
            ((PolynomialSite A B)ᵒᵖ ⥤ AddCommGrpCat.{u}) (0 : ℤ)).obj
          (kernelPresheaf A B))) :=
  sorry

end AbelianGroups

section Modules

variable [HasColimitsOfShape (PolynomialSite A B)ᵒᵖ (ModuleCat.{u} B)]
variable [HasDerivedCategory.{q'} (ModuleCat.{u} B)]
variable [HasDerivedCategory.{q} ((PolynomialSite A B)ᵒᵖ ⥤ ModuleCat.{u} B)]
variable [Functor.HasLeftDerivedFunctor
  (categoryOverPointColimitToDerived (PolynomialSite A B) (ModuleCat.{u} B))
  (HomotopyCategory.quasiIso ((PolynomialSite A B)ᵒᵖ ⥤ ModuleCat.{u} B)
    (ComplexShape.up ℤ))]

/-- Degree-zero homology of the derived lower shriek of the conormal presheaf vanishes. -/
@[stacks 08R7]
theorem conormal_homology_zero_isZero :
    IsZero
      ((DerivedCategory.homologyFunctor (ModuleCat.{u} B) (0 : ℤ)).obj
        (((DerivedCategory.singleFunctor
            ((PolynomialSite A B)ᵒᵖ ⥤ ModuleCat.{u} B) (0 : ℤ)) ⋙
          Lπ![(PolynomialSite A B), (ModuleCat.{u} B)]).obj
          (conormalSheaf A B))) :=
  sorry

/-- Degree-one homology of the derived lower shriek of the conormal presheaf vanishes. -/
@[stacks 08R7]
theorem conormal_homology_negOne_isZero :
    IsZero
      ((DerivedCategory.homologyFunctor (ModuleCat.{u} B) (-1 : ℤ)).obj
        (((DerivedCategory.singleFunctor
            ((PolynomialSite A B)ᵒᵖ ⥤ ModuleCat.{u} B) (0 : ℤ)) ⋙
          Lπ![(PolynomialSite A B), (ModuleCat.{u} B)]).obj
          (conormalSheaf A B))) :=
  sorry

end Modules

end Algebra.PolynomialSite
