/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.Algebra.PolynomialSite.Differentials
public import ReasLib.Algebra.PolynomialTower
public import Mathlib.Algebra.Category.ModuleCat.ChangeOfRings
public import Mathlib.Algebra.Homology.ShortComplex.ShortExact
public import Mathlib.RingTheory.Kaehler.TensorProduct
public import Mathlib.CategoryTheory.Preadditive.AdditiveFunctor
public import Mathlib.CategoryTheory.Sites.Abelian
import Mathlib.CategoryTheory.Abelian.FunctorCategory
import Mathlib.CategoryTheory.Limits.FunctorCategory.EpiMono
import Mathlib.Algebra.Homology.ShortComplex.Abelian
import Mathlib.Algebra.Homology.ShortComplex.ModuleCat
import Mathlib.Algebra.Category.ModuleCat.Abelian
import Mathlib.RingTheory.Smooth.Basic
import Mathlib.RingTheory.Kaehler.JacobiZariski

/-!
# Differential transitivity on polynomial squares

The three projections of polynomial squares carry a canonical sequence of
scalar-extended differential modules, and hence a sequence of sheaves for the bottom topology.
-/

@[expose] public section

open CategoryTheory Opposite
open CommAlgCat.Over.Polynomial.Site
open scoped TensorProduct ChangeOfRings

noncomputable section

universe u

set_option backward.privateInPublic true
set_option backward.isDefEq.respectTransparency false

namespace Algebra.PolynomialTower

variable (A B C : Type u) [CommRing A] [CommRing B] [CommRing C]
variable [Algebra A B] [Algebra B C] [Algebra A C] [IsScalarTower A B C]

/-- Differentials of the first polynomial algebra, extended to the intermediate base. -/
def inverseImageOmega1 : PolynomialTower A B C ⥤ ModuleCat.{u} B :=
  forgetToBase A B C ⋙ omegaSheafCov A B

/-- Differentials of the second polynomial algebra over the initial base, extended to the target. -/
def inverseImageOmega2 : PolynomialTower A B C ⥤ ModuleCat.{u} C :=
  forgetToOverA A B C ⋙ omegaSheafCov A C

/-- Relative differentials after tensor base change to the intermediate base. -/
def inverseImageOmega3 : PolynomialTower A B C ⥤ ModuleCat.{u} C :=
  forgetToOverB A B C ⋙ omegaSheafCov B C

/-- The first differential functor evaluates on the first augmented polynomial algebra. -/
theorem inverseImageOmega1_obj (X : PolynomialTower A B C) :
    (inverseImageOmega1 A B C).obj X = omegaSheafObj (base X) := rfl

/-- The second differential functor evaluates on the second augmented polynomial algebra. -/
theorem inverseImageOmega2_obj (X : PolynomialTower A B C) :
    (inverseImageOmega2 A B C).obj X = omegaSheafObj (overA X) := rfl

/-- The relative differential functor evaluates on the tensor base change. -/
theorem inverseImageOmega3_obj (X : PolynomialTower A B C) :
    (inverseImageOmega3 A B C).obj X = omegaSheafObj (tensorOverBase X) := rfl

/-- The first differential module extended further to the final target ring. -/
def tensorOmega1Obj (X : PolynomialTower A B C) : ModuleCat.{u} C :=
  (ModuleCat.extendScalars (algebraMap B C)).obj ((inverseImageOmega1 A B C).obj X)

/-- Extension of scalars of the first differential functor to the final target ring. -/
def tensorOmega1 : PolynomialTower A B C ⥤ ModuleCat.{u} C :=
  inverseImageOmega1 A B C ⋙ ModuleCat.extendScalars (algebraMap B C)

/-- Evaluation commutes with extension of scalars of the first differential functor. -/
theorem tensorOmega1_obj (X : PolynomialTower A B C) :
    (tensorOmega1 A B C).obj X = tensorOmega1Obj A B C X := rfl

/-- The first term is the scalar extension of the first inverse-image differential functor. -/
theorem tensorOmega1_eq_extendScalars :
    tensorOmega1 A B C =
      inverseImageOmega1 A B C ⋙ ModuleCat.extendScalars (algebraMap B C) := rfl

variable {A B C}

private instance algebraPQ (X : PolynomialTower A B C) : Algebra (P X) (Q X) :=
  (toQ X).hom.toRingHom.toAlgebra

private instance algebraPB (X : PolynomialTower A B C) : Algebra (P X) B :=
  algebraToBase (base X)

private instance algebraQC (X : PolynomialTower A B C) : Algebra (Q X) C :=
  algebraToBase (overA X)

private instance algebraPC (X : PolynomialTower A B C) : Algebra (P X) C :=
  ((toC X).hom.toRingHom.comp (toQ X).hom.toRingHom).toAlgebra

private instance towerAPQ (X : PolynomialTower A B C) : IsScalarTower A (P X) (Q X) :=
  IsScalarTower.of_algHom (toQ X).hom

private instance towerPQC (X : PolynomialTower A B C) : IsScalarTower (P X) (Q X) C :=
  IsScalarTower.of_algebraMap_eq fun _ ↦ rfl

private instance towerPBC (X : PolynomialTower A B C) : IsScalarTower (P X) B C :=
  IsScalarTower.of_algebraMap_eq fun p ↦ (toCOverP_commutes X p).symm

private instance towerAQC (X : PolynomialTower A B C) : IsScalarTower A (Q X) C :=
  IsScalarTower.of_algHom (toC X).hom

private instance algebraQTensor (X : PolynomialTower A B C) :
    Algebra (Q X) (tensorOverBase X).obj.left :=
  by
    change Algebra (Q X) ((Q X) ⊗[P X] B)
    exact Algebra.TensorProduct.leftAlgebra

private instance algebraPTensor (X : PolynomialTower A B C) :
    Algebra (P X) (tensorOverBase X).obj.left :=
  by
    change Algebra (P X) ((Q X) ⊗[P X] B)
    exact Algebra.TensorProduct.instAlgebra

private instance towerPQTensor (X : PolynomialTower A B C) :
    IsScalarTower (P X) (Q X) (tensorOverBase X).obj.left := by
  change IsScalarTower (P X) (Q X) ((Q X) ⊗[P X] B)
  infer_instance

private instance towerPBTensor (X : PolynomialTower A B C) :
    IsScalarTower (P X) B (tensorOverBase X).obj.left := by
  change @IsScalarTower (P X) B ((Q X) ⊗[P X] B) _
    (Algebra.TensorProduct.rightAlgebra (R := P X) (A := Q X) (B := B)).toSMul _
  exact Algebra.TensorProduct.right_isScalarTower

private instance pushoutTensor (X : PolynomialTower A B C) :
    Algebra.IsPushout (P X) B (Q X) (tensorOverBase X).obj.left := by
  exact @TensorProduct.isPushout' (P X) (Q X) B _ _ _ (algebraPQ X) (algebraPB X)

private instance algebraTensorC (X : PolynomialTower A B C) :
    Algebra (tensorOverBase X).obj.left C :=
  algebraToBase (tensorOverBase X)

private instance towerQTensorC (X : PolynomialTower A B C) :
    IsScalarTower (Q X) (tensorOverBase X).obj.left C :=
  IsScalarTower.of_algebraMap_eq fun q ↦ by
    change toC X q = toC X q * algebraMap B C 1
    simp

private def extendScalarsObjIso (M : ModuleCat.{u} B) :
    (ModuleCat.extendScalars (algebraMap B C)).obj M ≅ ModuleCat.of C (C ⊗[B] M) :=
  eqToIso (by
    have h : Module.compHom C (algebraMap B C) = (inferInstance : Module B C) :=
      Module.ext' _ _ fun b c ↦ (Algebra.smul_def b c).symm
    let F (m : Module B C) (hc : @SMulCommClass B C C m.toSMul _) : ModuleCat.{u} C :=
      @ModuleCat.of C _ (@TensorProduct B _ C M _ _ m _) _
        (@TensorProduct.leftModule B C _ _ C M _ _ _ m _ hc)
    change F (Module.compHom C (algebraMap B C))
      (@SMulCommClass.mk B C C (Module.compHom C (algebraMap B C)).toSMul _
        (fun b c x ↦ by
          change algebraMap B C b * (c * x) = c * (algebraMap B C b * x)
          rw [← mul_assoc, mul_comm (algebraMap B C b) c, mul_assoc])) = F _ _
    congr 1)

private theorem extendScalarsObjIso_tmul (M : ModuleCat.{u} B) (c : C) (m : M) :
    (extendScalarsObjIso M).hom.hom (c ⊗ₜ[B, algebraMap B C] m) = c ⊗ₜ[B] m := by
  let F (a : Module B C) (hc : @SMulCommClass B C C a.toSMul _) : ModuleCat.{u} C :=
    @ModuleCat.of C _ (@TensorProduct B _ C M _ _ a _) _
      (@TensorProduct.leftModule B C _ _ C M _ _ _ a _ hc)
  have transport (a₁ a₂ : Module B C)
      (hc₁ : @SMulCommClass B C C a₁.toSMul _)
      (hc₂ : @SMulCommClass B C C a₂.toSMul _)
      (h : a₁ = a₂) (e : F a₁ hc₁ = F a₂ hc₂) :
      (eqToHom e).hom (@TensorProduct.tmul B _ C M _ _ a₁ _ c m) =
        @TensorProduct.tmul B _ C M _ _ a₂ _ c m := by
    subst a₂
    rfl
  have h : Module.compHom C (algebraMap B C) = (inferInstance : Module B C) :=
    Module.ext' _ _ fun b c ↦ (Algebra.smul_def b c).symm
  exact transport (Module.compHom C (algebraMap B C)) (inferInstance : Module B C) _ _ h
    (by congr 1)

private theorem omegaSheafMap_tmul_D_formula {X Y : Algebra.PolynomialOver A B} (f : X ⟶ Y)
    (b : B) (x : X.obj.left) :
    (omegaSheafMap f).hom
      (@TensorProduct.tmul X.obj.left _ B (KaehlerDifferential A X.obj.left) _ _
        (algebraToBase X).toModule _ b (KaehlerDifferential.D A X.obj.left x)) =
      @TensorProduct.tmul Y.obj.left _ B (KaehlerDifferential A Y.obj.left) _ _
        (algebraToBase Y).toModule _ b
          (KaehlerDifferential.D A Y.obj.left (f.hom.left x)) := by
  letI := algebraToBase X
  letI := algebraToBase Y
  letI := algebraOfHom f
  letI := algebraOfHom_isScalarTower f
  letI := toBase_isScalarTower f
  change KaehlerDifferential.tensorMapBaseChange A X.obj.left Y.obj.left B
    (b ⊗ₜ[X.obj.left] KaehlerDifferential.D A X.obj.left x) = _
  rw [KaehlerDifferential.tensorMapBaseChange_tmul, KaehlerDifferential.map_D]
  rfl

private theorem tensorKaehler_ext {R S T M : Type u}
    [CommRing R] [CommRing S] [CommRing T] [Algebra R S] [Algebra S T]
    [AddCommGroup M] [Module T M]
    {f g : T ⊗[S] KaehlerDifferential R S →ₗ[T] M}
    (h : ∀ t s, f (t ⊗ₜ[S] KaehlerDifferential.D R S s) =
      g (t ⊗ₜ[S] KaehlerDifferential.D R S s)) : f = g := by
  apply LinearMap.ext
  intro z
  induction z using TensorProduct.induction_on with
  | zero => simp
  | add z z' hz hz' => simpa only [map_add, hz, hz']
  | tmul t w =>
    have hw : w ∈ Submodule.span S (Set.range (KaehlerDifferential.D R S)) := by
      rw [KaehlerDifferential.span_range_derivation]
      trivial
    revert t
    refine Submodule.span_induction ?_ ?_ ?_ ?_ hw
    · rintro _ ⟨s, rfl⟩ t
      exact h t s
    · intro t
      simp
    · intro w w' _ _ hw hw' t
      simpa only [TensorProduct.tmul_add, map_add] using congrArg₂ (· + ·) (hw t) (hw' t)
    · intro s w _ hw t
      simpa only [TensorProduct.tmul_smul, TensorProduct.smul_tmul'] using hw (s • t)

variable (A B C)

/-- The first transitivity map is differential functoriality followed by scalar-extension cancellation. -/
def toOmega2App (X : PolynomialTower A B C) :
    (tensorOmega1 A B C).obj X ⟶ (inverseImageOmega2 A B C).obj X :=
  (extendScalarsObjIso ((inverseImageOmega1 A B C).obj X)).hom ≫
    ModuleCat.ofHom
      (KaehlerDifferential.tensorMapBaseChange A (P X) (Q X) C ∘ₗ
        (TensorProduct.AlgebraTensorModule.cancelBaseChange
          (P X) B C C (KaehlerDifferential A (P X))).toLinearMap)

/-- The first map sends a double tensor of a differential to the differential of its image. -/
theorem toOmega2App_tmul_D (X : PolynomialTower A B C) (c : C) (b : B) (p : P X) :
    (toOmega2App A B C X).hom
      (c ⊗ₜ[B, algebraMap B C]
        (show (inverseImageOmega1 A B C).obj X from
          (show B ⊗[P X] KaehlerDifferential A (P X) from
            b ⊗ₜ[P X] KaehlerDifferential.D A (P X) p))) =
      (c * algebraMap B C b) ⊗ₜ[Q X] KaehlerDifferential.D A (Q X) (toQ X p) := by
  change KaehlerDifferential.tensorMapBaseChange A (P X) (Q X) C
    (TensorProduct.AlgebraTensorModule.cancelBaseChange (P X) B C C _
      ((extendScalarsObjIso (ModuleCat.of B (B ⊗[P X] KaehlerDifferential A (P X)))).hom.hom
        (c ⊗ₜ[B, algebraMap B C] (b ⊗ₜ[P X] KaehlerDifferential.D A (P X) p)))) = _
  rw [extendScalarsObjIso_tmul, TensorProduct.AlgebraTensorModule.cancelBaseChange_tmul,
    KaehlerDifferential.tensorMapBaseChange_tmul, KaehlerDifferential.map_D]
  simp [Algebra.smul_def, mul_comm]
  rfl

/-- The first transitivity map commutes with morphisms of polynomial squares. -/
theorem toOmega2_naturality {X Y : PolynomialTower A B C} (f : X ⟶ Y) :
    (tensorOmega1 A B C).map f ≫ toOmega2App A B C Y =
      toOmega2App A B C X ≫ (inverseImageOmega2 A B C).map f := by
  apply ModuleCat.hom_ext
  apply LinearMap.ext
  intro z
  change @TensorProduct B _ C (B ⊗[P X] KaehlerDifferential A (P X)) _ _
    (Module.compHom C (algebraMap B C)) _ at z
  induction z using TensorProduct.induction_on with
  | zero => simp
  | add z z' hz hz' => simpa only [map_add, hz, hz']
  | tmul c m =>
    induction m using TensorProduct.induction_on with
    | zero => simp
    | add m m' hm hm' => simpa only [TensorProduct.tmul_add, map_add, hm, hm']
    | tmul b w =>
      have hw : w ∈ Submodule.span (P X) (Set.range (KaehlerDifferential.D A (P X))) := by
        rw [KaehlerDifferential.span_range_derivation]
        trivial
      revert b
      refine Submodule.span_induction ?_ ?_ ?_ ?_ hw
      · rintro _ ⟨p, rfl⟩ b
        have hP := omegaSheafMap_tmul_D_formula ((forgetToBase A B C).map f) b p
        have hX := toOmega2App_tmul_D A B C X c b p
        have hY := toOmega2App_tmul_D A B C Y c b (mapP f p)
        have hQ := omegaSheafMap_tmul_D_formula ((forgetToOverA A B C).map f)
          (c * algebraMap B C b) (toQ X p)
        have hpq : mapQ f (toQ X p) = toQ Y (mapP f p) :=
          (congrArg (fun g : P X ⟶ Q Y ↦ g p) f.hom.left.w).symm
        calc
          _ = (toOmega2App A B C Y).hom
              (c ⊗ₜ[B, algebraMap B C] (show B ⊗[P Y] KaehlerDifferential A (P Y) from
                b ⊗ₜ[P Y] KaehlerDifferential.D A (P Y) (mapP f p))) :=
            congrArg (fun m : omegaSheafObj (base Y) ↦
              (toOmega2App A B C Y).hom (c ⊗ₜ[B, algebraMap B C] m)) hP
          _ = (c * algebraMap B C b) ⊗ₜ[Q Y]
              KaehlerDifferential.D A (Q Y) (toQ Y (mapP f p)) := hY
          _ = (c * algebraMap B C b) ⊗ₜ[Q Y]
              KaehlerDifferential.D A (Q Y) (mapQ f (toQ X p)) :=
            congrArg (fun q : Q Y ↦ (c * algebraMap B C b) ⊗ₜ[Q Y]
              KaehlerDifferential.D A (Q Y) q) hpq.symm
          _ = _ := ((congrArg (omegaSheafMap ((forgetToOverA A B C).map f)).hom hX).trans hQ).symm
      · intro b
        simp
      · intro w w' _ _ hw hw' b
        simpa only [TensorProduct.tmul_add, map_add] using congrArg₂ (· + ·) (hw b) (hw' b)
      · intro p w _ hw b
        simpa only [TensorProduct.tmul_smul, TensorProduct.smul_tmul'] using hw (p • b)

/-- The natural first transitivity map on polynomial squares. -/
def toOmega2 : tensorOmega1 A B C ⟶ inverseImageOmega2 A B C where
  app := toOmega2App A B C
  naturality _ _ f := toOmega2_naturality A B C f

/-- Differential base change identifies the relative differential module with the third term. -/
def omega3Iso (X : PolynomialTower A B C) :
    ModuleCat.of C (C ⊗[Q X] KaehlerDifferential (P X) (Q X)) ≅
      (inverseImageOmega3 A B C).obj X :=
  (TensorProduct.AlgebraTensorModule.cancelBaseChange
    (Q X) (tensorOverBase X).obj.left C C (KaehlerDifferential (P X) (Q X))).symm.toModuleIso ≪≫
    ((KaehlerDifferential.tensorKaehlerEquiv (P X) B (Q X) (tensorOverBase X).obj.left).baseChange
      (tensorOverBase X).obj.left C _ _).toModuleIso

/-- Differential base change sends a differential to the differential of the left tensor inclusion. -/
theorem omega3Iso_tmul_D (X : PolynomialTower A B C) (c : C) (q : Q X) :
    (omega3Iso A B C X).hom (c ⊗ₜ[Q X] KaehlerDifferential.D (P X) (Q X) q) =
      c ⊗ₜ[(tensorOverBase X).obj.left]
        KaehlerDifferential.D B (tensorOverBase X).obj.left
          (Algebra.TensorProduct.includeLeftRingHom q) := by
  change (KaehlerDifferential.tensorKaehlerEquiv (P X) B (Q X)
    (tensorOverBase X).obj.left).baseChange (tensorOverBase X).obj.left C _ _
      ((TensorProduct.AlgebraTensorModule.cancelBaseChange (Q X)
        (tensorOverBase X).obj.left C C _).symm
          (c ⊗ₜ[Q X] KaehlerDifferential.D (P X) (Q X) q)) = _
  rw [TensorProduct.AlgebraTensorModule.cancelBaseChange_symm_tmul,
    LinearEquiv.baseChange_tmul, KaehlerDifferential.tensorKaehlerEquiv_tmul_D]
  simp only [one_smul]
  rfl

/-- The second transitivity map is the relative differential map followed by differential base change. -/
def toOmega3App (X : PolynomialTower A B C) :
    (inverseImageOmega2 A B C).obj X ⟶ (inverseImageOmega3 A B C).obj X :=
  by
  change ModuleCat.of C (C ⊗[Q X] KaehlerDifferential A (Q X)) ⟶ _
  exact ModuleCat.ofHom ((KaehlerDifferential.map A (P X) (Q X) (Q X)).baseChange C) ≫
    (omega3Iso A B C X).hom

/-- The second map sends a differential to its relative differential in the tensor base change. -/
theorem toOmega3App_tmul_D (X : PolynomialTower A B C) (c : C) (q : Q X) :
    (toOmega3App A B C X).hom (show C ⊗[Q X] KaehlerDifferential A (Q X) from
      c ⊗ₜ[Q X] KaehlerDifferential.D A (Q X) q) =
      c ⊗ₜ[(tensorOverBase X).obj.left]
        KaehlerDifferential.D B (tensorOverBase X).obj.left
          (Algebra.TensorProduct.includeLeftRingHom q) := by
  change (omega3Iso A B C X).hom.hom
    (((KaehlerDifferential.map A (P X) (Q X) (Q X)).baseChange C)
      (c ⊗ₜ[Q X] KaehlerDifferential.D A (Q X) q)) = _
  rw [LinearMap.baseChange_tmul, KaehlerDifferential.map_D]
  exact omega3Iso_tmul_D A B C X c q

/-- The second transitivity map commutes with morphisms of polynomial squares. -/
theorem toOmega3_naturality {X Y : PolynomialTower A B C} (f : X ⟶ Y) :
    (inverseImageOmega2 A B C).map f ≫ toOmega3App A B C Y =
      toOmega3App A B C X ≫ (inverseImageOmega3 A B C).map f := by
  apply ModuleCat.hom_ext
  apply tensorKaehler_ext (R := A) (S := Q X) (T := C)
  intro c q
  have hQ := omegaSheafMap_tmul_D_formula ((forgetToOverA A B C).map f) c q
  have hX := toOmega3App_tmul_D A B C X c q
  have hY := toOmega3App_tmul_D A B C Y c (mapQ f q)
  have hT := omegaSheafMap_tmul_D_formula ((forgetToOverB A B C).map f) c
    (Algebra.TensorProduct.includeLeftRingHom q)
  have ht : ((forgetToOverB A B C).map f).hom.left.hom
      (Algebra.TensorProduct.includeLeftRingHom q) =
        Algebra.TensorProduct.includeLeftRingHom (mapQ f q) :=
    forgetToOverB_map_tmul f q 1
  have hm := congrArg (fun t : (tensorOverBase Y).obj.left ↦
    c ⊗ₜ[(tensorOverBase Y).obj.left]
      KaehlerDifferential.D B (tensorOverBase Y).obj.left t) ht.symm
  exact ((congrArg (toOmega3App A B C Y).hom hQ).trans hY).trans
    (hm.trans ((congrArg (omegaSheafMap ((forgetToOverB A B C).map f)).hom hX).trans hT).symm)

/-- The natural second transitivity map on polynomial squares. -/
def toOmega3 : inverseImageOmega2 A B C ⟶ inverseImageOmega3 A B C where
  app := toOmega3App A B C
  naturality _ _ f := toOmega3_naturality A B C f

/-- The composite of the two differential transitivity maps vanishes. -/
theorem omegaSequence_zero : toOmega2 A B C ≫ toOmega3 A B C = 0 := by
  apply NatTrans.ext
  funext X
  apply ModuleCat.hom_ext
  apply LinearMap.ext
  intro z
  change @TensorProduct B _ C (B ⊗[P X] KaehlerDifferential A (P X)) _ _
    (Module.compHom C (algebraMap B C)) _ at z
  induction z using TensorProduct.induction_on with
  | zero => simp
  | add z z' hz hz' => simpa only [map_add, hz, hz']
  | tmul c m =>
    induction m using TensorProduct.induction_on with
    | zero => simp
    | add m m' hm hm' => simpa only [TensorProduct.tmul_add, map_add, hm, hm']
    | tmul b w =>
      have hw : w ∈ Submodule.span (P X) (Set.range (KaehlerDifferential.D A (P X))) := by
        rw [KaehlerDifferential.span_range_derivation]
        trivial
      revert b
      refine Submodule.span_induction ?_ ?_ ?_ ?_ hw
      · rintro _ ⟨p, rfl⟩ b
        have hX := toOmega2App_tmul_D A B C X c b p
        have hY := toOmega3App_tmul_D A B C X (c * algebraMap B C b) (toQ X p)
        have hp : Algebra.TensorProduct.includeLeftRingHom (toQ X p) =
            algebraMap B (tensorOverBase X).obj.left (toB X p) :=
          Algebra.TensorProduct.tmul_one_eq_one_tmul (R := P X) (A := Q X) (B := B) p
        have hd : KaehlerDifferential.D B (tensorOverBase X).obj.left
            (Algebra.TensorProduct.includeLeftRingHom (toQ X p)) = 0 :=
          (congrArg (KaehlerDifferential.D B (tensorOverBase X).obj.left) hp).trans
            ((KaehlerDifferential.D B (tensorOverBase X).obj.left).map_algebraMap (toB X p))
        calc
          _ = _ := (congrArg (toOmega3App A B C X).hom hX).trans hY
          _ = (c * algebraMap B C b) ⊗ₜ[(tensorOverBase X).obj.left]
              (0 : KaehlerDifferential B (tensorOverBase X).obj.left) :=
            congrArg (fun w : KaehlerDifferential B (tensorOverBase X).obj.left ↦
              (c * algebraMap B C b) ⊗ₜ[(tensorOverBase X).obj.left] w) hd
          _ = 0 := TensorProduct.tmul_zero _ _
      · intro b
        simp
      · intro w w' _ _ hw hw' b
        simpa only [TensorProduct.tmul_add, map_add] using congrArg₂ (· + ·) (hw b) (hw' b)
      · intro p w _ hw b
        simpa only [TensorProduct.tmul_smul, TensorProduct.smul_tmul'] using hw (p • b)

/-- The differential transitivity complex of functors on polynomial squares. -/
def omegaSequence : ShortComplex (PolynomialTower A B C ⥤ ModuleCat.{u} C) :=
  ShortComplex.mk (toOmega2 A B C) (toOmega3 A B C) (omegaSequence_zero A B C)

/-- Evaluation of the differential transitivity complex at a polynomial square. -/
def omegaSequence_app (X : PolynomialTower A B C) : ShortComplex (ModuleCat.{u} C) :=
  (omegaSequence A B C).map ((evaluation _ _).obj X)

/-- The differential transitivity complex is short exact at every polynomial square. -/
theorem omegaSequence_app_shortExact (X : PolynomialTower A B C) :
    (omegaSequence_app A B C X).ShortExact := by
  obtain ⟨σ, ⟨e⟩⟩ := X.property.2.exists_repr
  letI : Algebra.FormallySmooth (P X) (Q X) := Algebra.FormallySmooth.of_equiv e.symm
  let f := KaehlerDifferential.mapBaseChange A (P X) (Q X)
  let g := KaehlerDifferential.map A (P X) (Q X) (Q X)
  have hf : Function.Injective f := by
    apply (LinearMap.injective_iff_eq_zero_of_exact
      (Algebra.H1Cotangent.exact_δ_mapBaseChange A (P X) (Q X))).mpr
    ext x
    have hx : x = 0 := Subsingleton.elim _ _
    simp [hx]
  have hg : Function.Surjective g := KaehlerDifferential.map_surjective A (P X) (Q X)
  have hfg : Function.Exact f g := KaehlerDifferential.exact_mapBaseChange_map A (P X) (Q X)
  obtain ⟨s, hs⟩ := Module.projective_lifting_property g LinearMap.id hg
  obtain ⟨r, hr⟩ := ((hfg.split_tfae'.out 0 1 rfl rfl).mp ⟨hf, s, hs⟩).2
  have hfC : Function.Injective (f.baseChange C) := by
    have h : (r.baseChange C).comp (f.baseChange C) = LinearMap.id := by
      rw [← LinearMap.baseChange_comp, hr, LinearMap.baseChange_id]
    exact (show Function.LeftInverse (r.baseChange C) (f.baseChange C) from
      LinearMap.congr_fun h).injective
  have hgC : Function.Surjective (g.baseChange C) := by
    simpa only [LinearMap.baseChange_eq_ltensor] using LinearMap.lTensor_surjective C hg
  have hfgC : Function.Exact (f.baseChange C) (g.baseChange C) := by
    simpa only [LinearMap.baseChange_eq_ltensor] using lTensor_exact C hfg hg
  let e₁ : (tensorOmega1 A B C).obj X ≃ₗ[C]
      C ⊗[Q X] ((Q X) ⊗[P X] KaehlerDifferential A (P X)) :=
    ((extendScalarsObjIso ((inverseImageOmega1 A B C).obj X)).toLinearEquiv.trans
      (TensorProduct.AlgebraTensorModule.cancelBaseChange (P X) B C C
        (KaehlerDifferential A (P X)))).trans
          (TensorProduct.AlgebraTensorModule.cancelBaseChange (P X) (Q X) C C
            (KaehlerDifferential A (P X))).symm
  let e₃ := (omega3Iso A B C X).toLinearEquiv
  refine { exact := ?_, mono_f := ?_, epi_g := ?_ }
  · apply (ShortComplex.ShortExact.moduleCat_exact_iff_function_exact _).mpr
    change Function.Exact ((f.baseChange C).comp e₁.toLinearMap)
      (e₃.toLinearMap.comp (g.baseChange C))
    exact e₃.injective.comp_exact_iff_exact.mpr
      (e₁.surjective.comp_exact_iff_exact.mpr hfgC)
  · apply (ModuleCat.mono_iff_injective _).mpr
    change Function.Injective ((f.baseChange C).comp e₁.toLinearMap)
    exact hfC.comp e₁.injective
  · apply (ModuleCat.epi_iff_surjective _).mpr
    change Function.Surjective (e₃.toLinearMap.comp (g.baseChange C))
    exact e₃.surjective.comp hgC

/-- The differential transitivity complex is short exact in the functor category. -/
theorem omegaSequence_shortExact : (omegaSequence A B C).ShortExact := by
  let S := omegaSequence A B C
  have h (X : PolynomialTower A B C) :
      (S.map ((evaluation _ _).obj X)).ShortExact :=
    omegaSequence_app_shortExact A B C X
  refine { exact := ?_, mono_f := ?_, epi_g := ?_ }
  · rw [S.exact_iff_isZero_homology, Limits.IsZero.iff_id_eq_zero]
    apply NatTrans.ext
    funext X
    have hz := ((S.map ((evaluation _ _).obj X)).exact_iff_isZero_homology.mp
      (h X).exact).of_iso (S.mapHomologyIso ((evaluation _ _).obj X)).symm
    exact hz.eq_of_src _ _
  · haveI (X : PolynomialTower A B C) : Mono (S.f.app X) := (h X).mono_f
    exact NatTrans.mono_of_mono_app S.f
  · haveI (X : PolynomialTower A B C) : Epi (S.g.app X) := (h X).epi_g
    exact NatTrans.epi_of_epi_app S.g

/-- The differential transitivity complex as module-valued sheaves on the opposite polynomial-square site. -/
def omegaSheafSequence : ShortComplex
    (Sheaf (⊥ : GrothendieckTopology (PolynomialTower A B C)ᵒᵖ) (ModuleCat.{u} C)) :=
  ((omegaSequence A B C).map
    ((Functor.whiskeringLeft _ _ _).obj (unopUnop (PolynomialTower A B C)))).map
      (sheafBotEquivalence (C := (PolynomialTower A B C)ᵒᵖ) (ModuleCat.{u} C)).inverse

/-- The canonical differential transitivity sequence of sheaves is short exact. -/
theorem omegaSheafSequence_shortExact : (omegaSheafSequence A B C).ShortExact := by
  exact ((omegaSequence_shortExact A B C).map_of_exact
    ((Functor.whiskeringLeft _ _ _).obj (unopUnop (PolynomialTower A B C)))).map_of_exact
      (sheafBotEquivalence (C := (PolynomialTower A B C)ᵒᵖ) (ModuleCat.{u} C)).inverse

end Algebra.PolynomialTower
