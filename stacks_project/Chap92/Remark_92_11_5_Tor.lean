/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import Mathlib.Algebra.Category.ModuleCat.Abelian
public import Mathlib.Algebra.Category.ModuleCat.Projective
public import Mathlib.Algebra.Homology.HomologicalComplex
public import Mathlib.CategoryTheory.Abelian.LeftDerived
public import Mathlib.CategoryTheory.Abelian.Projective.Resolution
public import Mathlib.LinearAlgebra.TensorProduct.Basic
public import ReasLib.Algebra.Category.ModuleCat.ChangeOfRings.Additive
public import ReasLib.Algebra.Category.ModuleCat.ChangeOfRings.Projective
public import ReasLib.Algebra.Category.ModuleCat.ChangeOfRings.Tensor
public import stacks_project.Chap92.Remark_92_11_1_Ideal

/-!
# Tor sheaves of the kernel ideal on the polynomial site

This leaf owns the sheaf `Tor_n^O(𝒥, underline{B})` on `C_{B/A}`, obtained objectwise as
left-derived extension of scalars of `Ker(P ⟶ B)` along `P ⟶ B`.
-/

@[expose] public section

open CategoryTheory Opposite
open CategoryTheory.Limits
open HomologicalComplex
open scoped TensorProduct

noncomputable section

universe u

namespace CommAlgCat.Over.Polynomial.Site

variable {A B : Type u} [CommRing A] [CommRing B] [Algebra A B]

/-- The objectwise derived scalar extension `Tor_n^P(Ker(P ⟶ B), B)`, in the presence of the
induced `P`-algebra structure on `B`. -/
def kernelTorObjWith (n : ℕ) (X : Algebra.PolynomialOver A B) [Algebra X.obj.left B] :
    ModuleCat.{u} B :=
  ((ModuleCat.extendScalars (algebraMap X.obj.left B)).leftDerived n).obj
    (ModuleCat.of X.obj.left (RingHom.ker (algebraMap X.obj.left B)))

/-- The objectwise derived scalar extension `Tor_n^P(Ker(P ⟶ B), B)`. -/
def kernelTorObj (n : ℕ) (X : Algebra.PolynomialOver A B) : ModuleCat.{u} B :=
  @kernelTorObjWith A B _ _ _ n X (algebraToBase X)

/-- Unfolding `kernelTorObj` recovers the unbundled left-derived extension of scalars. -/
theorem kernelTorObj_eq (n : ℕ) (X : Algebra.PolynomialOver A B) :
    kernelTorObj n X = @kernelTorObjWith A B _ _ _ n X (algebraToBase X) :=
  sorry

/-- The `P`-linear map `Ker(P ⟶ B) ⟶ Ker(P' ⟶ B)` induced by a morphism of polynomial arrows,
after restriction of scalars along `P ⟶ P'`. -/
def kernelRestrictMapWith {X Y : Algebra.PolynomialOver A B} (f : X ⟶ Y)
    [Algebra X.obj.left B] [Algebra Y.obj.left B] [Algebra X.obj.left Y.obj.left] :
    ModuleCat.of X.obj.left (RingHom.ker (algebraMap X.obj.left B)) ⟶
      (ModuleCat.restrictScalars (algebraMap X.obj.left Y.obj.left)).obj
        (ModuleCat.of Y.obj.left (RingHom.ker (algebraMap Y.obj.left B))) :=
  ModuleCat.semilinearMapAddEquiv (algebraMap X.obj.left Y.obj.left)
      (ModuleCat.of X.obj.left (RingHom.ker (algebraMap X.obj.left B)))
      (ModuleCat.of Y.obj.left (RingHom.ker (algebraMap Y.obj.left B)))
    { toFun := fun j ↦
        ⟨algebraMap X.obj.left Y.obj.left (j : X.obj.left), kernel_le_comapWith f j.2⟩
      map_add' := sorry
      map_smul' := sorry }

/-- Unfolding `kernelRestrictMapWith` recovers the underlying ring map on kernels. -/
theorem kernelRestrictMapWith_apply {X Y : Algebra.PolynomialOver A B} (f : X ⟶ Y)
    [Algebra X.obj.left B] [Algebra Y.obj.left B] [Algebra X.obj.left Y.obj.left]
    (j : RingHom.ker (algebraMap X.obj.left B)) :
    kernelRestrictMapWith f j =
      ⟨algebraMap X.obj.left Y.obj.left (j : X.obj.left), kernel_le_comapWith f j.2⟩ :=
  sorry

/-- A chain-map comparison from the image of a chosen projective resolution under extension of
scalars to the chosen projective resolution of the extended module. -/
def mapExtendScalarsToResolution {R S : Type u} [CommRing R] [CommRing S] (φ : R →+* S)
    (M : ModuleCat.{u} R) :
    ((ModuleCat.extendScalars φ).mapHomologicalComplex (ComplexShape.down ℕ)).obj
        (projectiveResolution M).complex ⟶
      (projectiveResolution ((ModuleCat.extendScalars φ).obj M)).complex :=
  let P := projectiveResolution M
  let Q := projectiveResolution ((ModuleCat.extendScalars φ).obj M)
  let K := (ModuleCat.extendScalars φ).mapHomologicalComplex (ComplexShape.down ℕ) |>.obj P.complex
  -- Local instance justification (proof-local temporary data): projectivity of `K.X 1` is a field of the chosen `ProjectiveResolution`, not a global instance.
  letI : Projective (K.X 1) :=
    (ModuleCat.extendScalars φ).projective_obj_of_projective (P.projective 1)
  ChainComplex.mkHom K Q.complex
    (@Projective.factorThru (ModuleCat.{u} S) _ (K.X 0)
      ((ModuleCat.extendScalars φ).obj M) (Q.complex.X 0)
      ((ModuleCat.extendScalars φ).projective_obj_of_projective (P.projective 0))
      ((ModuleCat.extendScalars φ).map (P.π.f 0)) (Q.π.f 0)
      (epi_of_isColimit_cofork Q.isColimitCokernelCofork))
    (Q.exact₀.liftFromProjective
      (K.d 1 0 ≫
        @Projective.factorThru (ModuleCat.{u} S) _ (K.X 0)
          ((ModuleCat.extendScalars φ).obj M) (Q.complex.X 0)
          ((ModuleCat.extendScalars φ).projective_obj_of_projective (P.projective 0))
          ((ModuleCat.extendScalars φ).map (P.π.f 0)) (Q.π.f 0)
          (epi_of_isColimit_cofork Q.isColimitCokernelCofork))
      sorry)
    sorry
    fun n p ↦
      -- Local instance justification (proof-local temporary data): projectivity of `K.X (n + 2)` is a field of the chosen `ProjectiveResolution`, not a global instance.
      letI : Projective (K.X (n + 2)) :=
        (ModuleCat.extendScalars φ).projective_obj_of_projective (P.projective (n + 2))
      ⟨(Q.exact_succ n).liftFromProjective (K.d (n + 2) (n + 1) ≫ p.2.1) sorry, sorry⟩

/-- The canonical comparison from left-derived of a composite extension of scalars to the
postcomposed left-derived functor. -/
def leftDerivedCompToPostcomposed {R S T : Type u} [CommRing R] [CommRing S] [CommRing T]
    (φ : R →+* S) (ψ : S →+* T) (n : ℕ) (M : ModuleCat.{u} R) :
    ((ModuleCat.extendScalars φ ⋙ ModuleCat.extendScalars ψ).leftDerived n).obj M ⟶
      ((ModuleCat.extendScalars ψ).leftDerived n).obj ((ModuleCat.extendScalars φ).obj M) :=
  ((projectiveResolution M).isoLeftDerivedObj
      (ModuleCat.extendScalars φ ⋙ ModuleCat.extendScalars ψ) n).hom ≫
    (HomologicalComplex.homologyFunctor (ModuleCat.{u} T) (ComplexShape.down ℕ) n).map
      (((ModuleCat.extendScalars ψ).mapHomologicalComplex (ComplexShape.down ℕ)).map
        (mapExtendScalarsToResolution φ M)) ≫
    ((projectiveResolution ((ModuleCat.extendScalars φ).obj M)).isoLeftDerivedObj
      (ModuleCat.extendScalars ψ) n).inv

/-- The map on `Tor_n^P(Ker(P ⟶ B), B)` induced by a morphism of polynomial arrows, in the
presence of the induced algebra structures. -/
def kernelTorMapWith (n : ℕ) {X Y : Algebra.PolynomialOver A B} (f : X ⟶ Y)
    [Algebra X.obj.left B] [Algebra Y.obj.left B] [Algebra X.obj.left Y.obj.left]
    [IsScalarTower A X.obj.left Y.obj.left]
    [IsScalarTower X.obj.left Y.obj.left B] :
    kernelTorObjWith n X ⟶ kernelTorObjWith n Y :=
  eqToHom
      (congrArg
        (fun ψ : X.obj.left →+* B ↦
          ((ModuleCat.extendScalars ψ).leftDerived n).obj
            (ModuleCat.of X.obj.left (RingHom.ker (algebraMap X.obj.left B))))
        (IsScalarTower.algebraMap_eq X.obj.left Y.obj.left B)) ≫
    (NatTrans.leftDerived
        (ModuleCat.extendScalarsComp (algebraMap X.obj.left Y.obj.left)
          (algebraMap Y.obj.left B)).hom n).app
      (ModuleCat.of X.obj.left (RingHom.ker (algebraMap X.obj.left B))) ≫
    leftDerivedCompToPostcomposed (algebraMap X.obj.left Y.obj.left)
      (algebraMap Y.obj.left B) n
      (ModuleCat.of X.obj.left (RingHom.ker (algebraMap X.obj.left B))) ≫
    ((ModuleCat.extendScalars (algebraMap Y.obj.left B)).leftDerived n).map
      ((ModuleCat.extendScalars (algebraMap X.obj.left Y.obj.left)).map (kernelRestrictMapWith f) ≫
        (ModuleCat.extendRestrictScalarsAdj (algebraMap X.obj.left Y.obj.left)).counit.app
          (ModuleCat.of Y.obj.left (RingHom.ker (algebraMap Y.obj.left B))))

/-- The map on `Tor_n^P(Ker(P ⟶ B), B)` induced by a morphism of polynomial arrows over `B`. -/
def kernelTorMap (n : ℕ) {X Y : Algebra.PolynomialOver A B} (f : X ⟶ Y) :
    kernelTorObj n X ⟶ kernelTorObj n Y :=
  @kernelTorMapWith A B _ _ _ n X Y f (algebraToBase X) (algebraToBase Y) (algebraOfHom f)
    (@isScalarTower_algebraOfHom A B _ _ _ X Y f (algebraOfHom f))
    (@isScalarTower_toBase A B _ _ _ X Y f (algebraOfHom f) (algebraToBase Y) (algebraToBase X))

/-- Unfolding `kernelTorMap` recovers the change-of-rings comparison on left-derived
extension of scalars. -/
theorem kernelTorMap_eq (n : ℕ) {X Y : Algebra.PolynomialOver A B} (f : X ⟶ Y) :
    kernelTorMap n f =
      @kernelTorMapWith A B _ _ _ n X Y f (algebraToBase X) (algebraToBase Y) (algebraOfHom f)
        (@isScalarTower_algebraOfHom A B _ _ _ X Y f (algebraOfHom f))
        (@isScalarTower_toBase A B _ _ _ X Y f (algebraOfHom f) (algebraToBase Y)
          (algebraToBase X)) :=
  sorry

/-- Identity morphisms act as the identity on objectwise Tor. -/
theorem kernelTorMap_id (n : ℕ) (X : Algebra.PolynomialOver A B) :
    kernelTorMap n (𝟙 X) = 𝟙 (kernelTorObj n X) :=
  sorry

/-- Composition of polynomial-arrow morphisms maps to composition of objectwise Tor maps. -/
theorem kernelTorMap_comp (n : ℕ) {X Y Z : Algebra.PolynomialOver A B} (f : X ⟶ Y) (g : Y ⟶ Z) :
    kernelTorMap n (f ≫ g) = kernelTorMap n f ≫ kernelTorMap n g :=
  sorry

variable (A B) in
/-- The covariant functor of objectwise `Tor_n^O(𝒥, underline{B})` on polynomial arrows
`P ⟶ B`. -/
def kernelTorCov (n : ℕ) : Algebra.PolynomialOver A B ⥤ ModuleCat.{u} B where
  obj := kernelTorObj n
  map f := kernelTorMap n f
  map_id X := kernelTorMap_id n X
  map_comp f g := kernelTorMap_comp n f g

/-- Objects of `kernelTorCov` are the objectwise Tor modules of the corresponding polynomial
arrow. -/
theorem kernelTorCov_obj (n : ℕ) (X : Algebra.PolynomialOver A B) :
    (kernelTorCov A B n).obj X = kernelTorObj n X :=
  sorry

variable (A B) in
/-- The sheaf `Tor_n^O(𝒥, underline{B})` on `C_{B/A}`, as a functor
`(PolynomialSite A B)ᵒᵖ ⥤ ModuleCat B`. -/
def kernelTorSheaf (n : ℕ) : (Algebra.PolynomialSite A B)ᵒᵖ ⥤ ModuleCat.{u} B :=
  unopUnop (Algebra.PolynomialOver A B) ⋙ kernelTorCov A B n

/-- Evaluating `kernelTorSheaf` on a double-opposite polynomial arrow recovers `kernelTorObj`. -/
theorem kernelTorSheaf_obj (n : ℕ) (X : (Algebra.PolynomialSite A B)ᵒᵖ) :
    (kernelTorSheaf A B n).obj X = kernelTorObj n (unop (unop X)) :=
  sorry

/-- `kernelTorSheaf` is precomposition of `kernelTorCov` with the double-opposite equivalence. -/
theorem kernelTorSheaf_eq (n : ℕ) :
    kernelTorSheaf A B n = unopUnop (Algebra.PolynomialOver A B) ⋙ kernelTorCov A B n :=
  sorry

/-- Components of `kernelTorSheaf` on morphisms are `kernelTorMap` of the underlying polynomial
arrow. -/
theorem kernelTorSheaf_map (n : ℕ) {X Y : (Algebra.PolynomialSite A B)ᵒᵖ} (f : X ⟶ Y) :
    (kernelTorSheaf A B n).map f = kernelTorMap n f.unop.unop :=
  sorry

/-- The canonical morphism `Tor_0^P(Ker(P ⟶ B), B) ⟶ J/J² ⊗_P B` obtained from
`leftDerivedZeroIsoSelf` and extension of scalars along `toCotangent`. -/
def kernelTorZeroHomWith (X : Algebra.PolynomialOver A B) [Algebra X.obj.left B] :
    kernelTorObjWith 0 X ⟶ conormalObjWith X :=
  ((ModuleCat.extendScalars (algebraMap X.obj.left B)).leftDerivedZeroIsoSelf).hom.app
      (ModuleCat.of X.obj.left (RingHom.ker (algebraMap X.obj.left B))) ≫
    (ModuleCat.extendScalars (algebraMap X.obj.left B)).map
      (ModuleCat.ofHom (RingHom.ker (algebraMap X.obj.left B)).toCotangent) ≫
    (ModuleCat.ExtendScalars.tensorIso
      (ModuleCat.of X.obj.left (RingHom.ker (algebraMap X.obj.left B)).Cotangent)).hom

/-- The canonical morphism `kernelTorZeroHomWith` is an isomorphism. -/
instance kernelTorZeroHomWith_isIso (X : Algebra.PolynomialOver A B) [Algebra X.obj.left B] :
    IsIso (kernelTorZeroHomWith X) :=
  sorry

/-- The objectwise identification `Tor_0^P(Ker(P ⟶ B), B) ≅ J/J² ⊗_P B`. -/
def kernelTorZeroIsoAppWith (X : Algebra.PolynomialOver A B) [Algebra X.obj.left B] :
    kernelTorObjWith 0 X ≅ conormalObjWith X :=
  asIso (kernelTorZeroHomWith X)

/-- The objectwise identification `Tor_0 ≅ 𝒥/𝒥²` of a polynomial arrow. -/
def kernelTorZeroIsoApp (X : Algebra.PolynomialOver A B) :
    kernelTorObj 0 X ≅ conormalObj X :=
  @kernelTorZeroIsoAppWith A B _ _ _ X (algebraToBase X)

/-- The forward morphism of `kernelTorZeroIsoAppWith` is `kernelTorZeroHomWith`. -/
theorem kernelTorZeroIsoAppWith_hom (X : Algebra.PolynomialOver A B) [Algebra X.obj.left B] :
    (kernelTorZeroIsoAppWith X).hom = kernelTorZeroHomWith X :=
  sorry

variable (A B) in
/-- The identification `Tor_0^O(𝒥, underline{B}) ≅ 𝒥/𝒥²` of sheaves on `C_{B/A}`. -/
def kernelTorZeroIso : kernelTorSheaf A B 0 ≅ conormalSheaf A B :=
  NatIso.ofComponents (fun X ↦ kernelTorZeroIsoApp (unop (unop X))) sorry

/-- Components of `kernelTorZeroIso` are the objectwise identifications `kernelTorZeroIsoApp`. -/
theorem kernelTorZeroIso_hom_app (X : (Algebra.PolynomialSite A B)ᵒᵖ) :
    (kernelTorZeroIso A B).hom.app X = (kernelTorZeroIsoApp (unop (unop X))).hom :=
  sorry

/-- Inverse components of `kernelTorZeroIso` are the objectwise inverse identifications. -/
theorem kernelTorZeroIso_inv_app (X : (Algebra.PolynomialSite A B)ᵒᵖ) :
    (kernelTorZeroIso A B).inv.app X = (kernelTorZeroIsoApp (unop (unop X))).inv :=
  sorry

end CommAlgCat.Over.Polynomial.Site
