/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.AlgebraicGeometry.RingedSite.Module.Derived.InternalHom.Bifunctor
public import ReasLib.Algebra.Homology.CochainComplex.Monoidal.Closed.Shift
public import ReasLib.Algebra.Category.ModuleCat.Sheaf.RingedSite.Graded.IntMonoidal
public import Mathlib.CategoryTheory.Triangulated.Opposite.Functor

/-!
# Actual shifts and triangles of derived sheaf internal Hom

The concrete cochain shift matrices are transported through actual K-injective model maps and
the existing model comparison. No monoidal or closed structure on the derived category is an
input. Source shifts use the negative shift prescribed by its triangulated opposite category.
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits CategoryTheory.MonoidalCategory Opposite
open SheafOfModules.RingedSite SheafOfModules.RingedSite.RingedSiteDerived
open scoped Pretriangulated.Opposite

noncomputable section

universe u v

set_option backward.isDefEq.respectTransparency false

namespace CategoryTheory.CochainComplex.InternalHom

section Homotopies

variable {A : Type*} [Category* A] [Preadditive A]
variable [MonoidalCategory A] [MonoidalPreadditive A] [MonoidalClosed A]
variable [HasZeroObject A] [HasProductsOfShape ℤ A]
variable [∀ X Y : GradedObject ℤ A, GradedObject.HasTensor X Y]
variable [∀ X Y Z : GradedObject ℤ A, GradedObject.HasGoodTensor₁₂Tensor X Y Z]
variable [∀ X Y Z : GradedObject ℤ A, GradedObject.HasGoodTensorTensor₂₃ X Y Z]
variable [∀ X Y Z W : GradedObject ℤ A, GradedObject.HasTensor₄ObjExt X Y Z W]
variable [∀ X, PreservesColimit (Functor.empty.{0} A) ((curriedTensor A).obj X)]
variable [∀ X, PreservesColimit (Functor.empty.{0} A) ((curriedTensor A).flip.obj X)]

/-- Postcomposition transports a homotopy through the explicit product-valued Hom complex. -/
def mapHomotopy (F : CochainComplex A ℤ)
    {I I' : CochainComplex A ℤ} {f g : I ⟶ I'} (h : Homotopy f g) :
    Homotopy (map F f) (map F g) where
  hom n m := Pi.lift fun i ↦
    Pi.π (family F I n) i ≫ (ihom (F.X i)).map (h.hom (i + n) (i + m))
  zero n m hnm := by
    apply Pi.hom_ext
    intro i
    simp only [Pi.lift_π, zero_comp]
    rw [h.zero _ _ (by
      intro hh
      apply hnm
      simp only [ComplexShape.up_Rel] at *
      omega)]
    simp
  comm n := by
    obtain ⟨m, rfl⟩ : ∃ m : ℤ, n = m + 1 := ⟨n - 1, by omega⟩
    rw [dNext_eq _ (show (ComplexShape.up ℤ).Rel (m + 1) (m + 1 + 1) from rfl),
      prevD_eq _ (show (ComplexShape.up ℤ).Rel m (m + 1) from rfl)]
    apply Pi.hom_ext
    intro i
    simp only [map, obj, CochainComplex.of_d, GradedObject.InternalHom.map,
      differential, Category.assoc, Pi.lift_π, Pi.lift_π_assoc,
      Preadditive.add_comp, Preadditive.comp_add, Linear.units_smul_comp,
      Linear.comp_units_smul]
    simp only [postDifferential, Category.assoc, ← Functor.map_comp_assoc,
      ← CategoryTheory.MonoidalClosed.curry_natural_right,
      ← CategoryTheory.MonoidalClosed.curry_natural_left,
      preDifferential, Category.assoc, Pi.lift_π_assoc]
    rw [MonoidalCategory.whisker_exchange_assoc]
    simp only [← MonoidalCategory.whiskerLeft_comp_assoc, Pi.lift_π]
    simp only [MonoidalCategory.whiskerLeft_comp, Category.assoc]
    rw [ihom.ev_naturality_assoc]
    have hleft (a b c : ℤ) (hab : a = b) :
        eqToHom (congrArg I.X hab) ≫ h.hom b c = h.hom a c := by
      subst b
      simp
    have hright (a b c : ℤ) (hbc : b = c) :
        h.hom a b ≫ eqToHom (congrArg I'.X hbc) = h.hom a c := by
      subst c
      simp
    rw [← eqToHom_map (ihom (F.X i)) (congrArg I.X (postDegree i (m + 1))),
      ← eqToHom_map (ihom (F.X i)) (congrArg I'.X (postDegree i m))]
    rw [← Functor.map_comp, ← Functor.map_comp]
    rw [hleft _ _ _ (postDegree i (m + 1)),
      hleft _ _ _ (preDegree i (m + 1)), hright _ _ _ (preDegree i m)]
    rw [← Functor.map_comp, Category.assoc]
    rw [HomologicalComplex.d_comp_eqToHom I'
      (show (ComplexShape.up ℤ).Rel (i + m) (i + (m + 1)) from by
        simp only [ComplexShape.up_Rel]; omega) rfl]
    have hh := h.comm (i + (m + 1))
    rw [dNext_eq _ (show (ComplexShape.up ℤ).Rel (i + (m + 1))
        (i + (m + 1) + 1) from rfl),
      prevD_eq _ (show (ComplexShape.up ℤ).Rel (i + m) (i + (m + 1)) from by
        simp only [ComplexShape.up_Rel]; omega)] at hh
    rw [Int.negOnePow_succ, Units.neg_smul, hh]
    haveI := (ihom.adjunction (F.X i)).right_adjoint_additive
    rw [Functor.map_add, Functor.map_add, Preadditive.comp_add, Preadditive.comp_add]
    abel

end Homotopies

section QuasiIsomorphisms

variable {A : Type*} [Category* A] [Abelian A]
variable [MonoidalCategory A] [MonoidalPreadditive A] [MonoidalClosed A]
variable [HasZeroObject A] [HasProductsOfShape ℤ A]
variable [∀ X Y : GradedObject ℤ A, GradedObject.HasTensor X Y]
variable [∀ X Y Z : GradedObject ℤ A, GradedObject.HasGoodTensor₁₂Tensor X Y Z]
variable [∀ X Y Z : GradedObject ℤ A, GradedObject.HasGoodTensorTensor₂₃ X Y Z]
variable [∀ X Y Z W : GradedObject ℤ A, GradedObject.HasTensor₄ObjExt X Y Z W]
variable [∀ X, PreservesColimit (Functor.empty.{0} A) ((curriedTensor A).obj X)]
variable [∀ X, PreservesColimit (Functor.empty.{0} A) ((curriedTensor A).flip.obj X)]

/-- Strict internal Hom preserves quasi-isomorphisms between K-injective targets. -/
theorem quasiIso_map_of_isKInjective (F : CochainComplex A ℤ)
    {I I' : CochainComplex A ℤ} [I.IsKInjective] [I'.IsKInjective]
    (f : I ⟶ I') (hf : QuasiIso f) : QuasiIso (map F f) := by
  obtain ⟨e, rfl⟩ := (_root_.CochainComplex.IsKInjective.quasiIso_iff f).mp hf
  let E : HomotopyEquiv (obj F I) (obj F I') := {
    hom := (functor F).map e.hom
    inv := (functor F).map e.inv
    homotopyHomInvId := by
      have hh : Homotopy ((functor F).map (e.hom ≫ e.inv))
          ((functor F).map (𝟙 I)) := mapHomotopy F e.homotopyHomInvId
      simpa only [Functor.map_comp, Functor.map_id, functor] using hh
    homotopyInvHomId := by
      have hh : Homotopy ((functor F).map (e.inv ≫ e.hom))
          ((functor F).map (𝟙 I')) := mapHomotopy F e.homotopyInvHomId
      simpa only [Functor.map_comp, Functor.map_id, functor] using hh }
  exact E.quasiIso_hom
end QuasiIsomorphisms

end CategoryTheory.CochainComplex.InternalHom

namespace RingedSite.Hom.ModuleDerived.InternalHom

variable {C : Type u} [Category.{v} C] {J : GrothendieckTopology C}
variable [J.HasSheafCompose (forget₂ CommRingCat.{max u v} RingCat.{max u v})]
variable [HasWeakSheafify J AddCommGrpCat.{max u v}]
variable [J.WEqualsLocallyBijective AddCommGrpCat.{max u v}]
variable {O : Sheaf J CommRingCat.{max u v}}

/-- The actual target shift comparison on the strict sheaf-Hom complexes. -/
def strictTargetShiftIso (F I : CochainComplex (ringedSiteModuleCategory J O) ℤ) (n : ℤ) :
    (strictInternalHom.obj (op F)).obj (I⟦n⟧) ≅
      ((strictInternalHom.obj (op F)).obj I)⟦n⟧ :=
  CochainComplex.InternalHom.targetShiftIso F I n

/-- The actual normalized negative-source shift comparison on strict sheaf-Hom complexes. -/
def strictSourceShiftIso (F I : CochainComplex (ringedSiteModuleCategory J O) ℤ) (n : ℤ) :
    (strictInternalHom.obj (op (F⟦-n⟧))).obj I ≅
      ((strictInternalHom.obj (op F)).obj I)⟦n⟧ :=
  CochainComplex.InternalHom.sourceShiftIso F I n

/-- Lift the canonical derived shift of a model to an actual cochain comparison with the
selected K-injective model of the shifted object. -/
def modelShiftMap (N : max J O) (n : ℤ) :
    (injectiveModel N)⟦n⟧ ⟶ injectiveModel (N⟦n⟧) :=
  liftToInjectiveModel ((injectiveModel N)⟦n⟧) (N⟦n⟧)
    ((Functor.commShiftIso
      (DerivedCategory.Q : CochainComplex (ringedSiteModuleCategory J O) ℤ ⥤ max J O) n).hom.app
        (injectiveModel N) ≫
      (shiftFunctor (max J O) n).map (injectiveModelIso N).hom)

set_option backward.isDefEq.respectTransparency false in
/-- The model-shift comparison has its displayed canonical isomorphism as derived image. -/
instance modelShiftMap_quasiIso (N : max J O) (n : ℤ) :
    QuasiIso (modelShiftMap N n) := by
  apply (DerivedCategory.isIso_Q_map_iff_quasiIso _ _).1
  let e : (DerivedCategory.Q :
      CochainComplex (ringedSiteModuleCategory J O) ℤ ⥤ max J O).obj
        ((injectiveModel N)⟦n⟧) ≅ N⟦n⟧ :=
    (Functor.commShiftIso
      (DerivedCategory.Q : CochainComplex (ringedSiteModuleCategory J O) ℤ ⥤ max J O) n).app
        (injectiveModel N) ≪≫
      (shiftFunctor (max J O) n).mapIso (injectiveModelIso N)
  have h : DerivedCategory.Q.map (modelShiftMap N n) =
      e.hom ≫ (injectiveModelIso (N⟦n⟧)).inv := by
    apply (cancel_mono (injectiveModelIso (N⟦n⟧)).hom).1
    simpa only [modelShiftMap, e, Iso.trans_hom, Functor.mapIso_hom, Iso.app_hom,
      Category.assoc, Iso.inv_hom_id, Category.comp_id] using
      (liftToInjectiveModel_fac ((injectiveModel N)⟦n⟧) (N⟦n⟧) e.hom)
  rw [h]
  infer_instance

/-- Actual postcomposition by the target model-shift comparison. -/
def targetModelShiftMap (M N : max J O) (n : ℤ) :
    objOfModels (injectiveModel M) ((injectiveModel N)⟦n⟧) ⟶
      objOfModels (injectiveModel M) (injectiveModel (N⟦n⟧)) :=
  DerivedCategory.Q.map
    ((strictInternalHom.obj (op (injectiveModel M))).map (modelShiftMap N n))

/-- Postcomposition by a quasi-isomorphism between K-injective targets induces a
quasi-isomorphism of strict sheaf internal-Hom complexes. -/
theorem strictInternalHom_quasiIso_postcomp
    (F : CochainComplex (ringedSiteModuleCategory J O) ℤ)
    {I I' : CochainComplex (ringedSiteModuleCategory J O) ℤ}
    [I.IsKInjective] [I'.IsKInjective] (f : I ⟶ I') (hf : QuasiIso f) :
    QuasiIso ((strictInternalHom.obj (op F)).map f) := by
  letI tensorExists : ∀ X Y : GradedObject ℤ (ringedSiteModuleCategory J O),
      GradedObject.HasTensor X Y :=
    fun _ _ _ ↦ HasColimitsOfShape.has_colimit _
  -- Local instance justification (defeq pin): Select the same left iterated-tensor certificate as strictInternalHom for its explicit closed structure.
  letI goodLeft : ∀ X Y Z : GradedObject ℤ (ringedSiteModuleCategory J O),
      GradedObject.HasGoodTensor₁₂Tensor X Y Z :=
    fun _ _ _ _ _ ↦ PreservesColimitsOfShape.preservesColimit
  -- Local instance justification (defeq pin): Select the same right iterated-tensor certificate as strictInternalHom for its explicit closed structure.
  letI goodRight : ∀ X Y Z : GradedObject ℤ (ringedSiteModuleCategory J O),
      GradedObject.HasGoodTensorTensor₂₃ X Y Z :=
    fun _ _ _ _ _ ↦ PreservesColimitsOfShape.preservesColimit
  -- Local instance justification (defeq pin): Select the same fourfold tensor-extensionality certificate as strictInternalHom for its explicit closed structure.
  letI tensorExt : ∀ X Y Z W : GradedObject ℤ (ringedSiteModuleCategory J O),
      GradedObject.HasTensor₄ObjExt X Y Z W :=
    fun _ _ _ _ _ _ ↦ PreservesColimitsOfShape.preservesColimit
  -- Local instance justification (defeq pin): Select the same left-tensor empty-colimit certificate as strictInternalHom for its explicit closed structure.
  letI preservesLeft : ∀ X, PreservesColimit (Functor.empty.{0} (ringedSiteModuleCategory J O))
      ((curriedTensor (ringedSiteModuleCategory J O)).obj X) :=
    fun _ ↦ PreservesColimitsOfShape.preservesColimit
  -- Local instance justification (defeq pin): Select the same right-tensor empty-colimit certificate as strictInternalHom for its explicit closed structure.
  letI preservesRight : ∀ X, PreservesColimit (Functor.empty.{0} (ringedSiteModuleCategory J O))
      ((curriedTensor (ringedSiteModuleCategory J O)).flip.obj X) :=
    fun _ ↦ PreservesColimitsOfShape.preservesColimit
  change QuasiIso (CochainComplex.InternalHom.map F f)
  exact CochainComplex.InternalHom.quasiIso_map_of_isKInjective F f hf

/-- A quasi-isomorphism between K-injective targets is a homotopy equivalence, so this
actual postcomposition map is invertible after passing to the derived category. -/
instance targetModelShiftMap_isIso (M N : max J O) (n : ℤ) :
    IsIso (targetModelShiftMap M N n) := by
  apply (DerivedCategory.isIso_Q_map_iff_quasiIso _ _).2
  exact strictInternalHom_quasiIso_postcomp
    (injectiveModel M) (modelShiftMap N n) (modelShiftMap_quasiIso N n)

/-- Actual precomposition by the negative-source model-shift comparison. -/
def sourceModelShiftMap (M N : max J O) (n : ℤ) :
    objOfModels (injectiveModel (M⟦-n⟧)) (injectiveModel N) ⟶
      objOfModels ((injectiveModel M)⟦-n⟧) (injectiveModel N) :=
  DerivedCategory.Q.map
    ((strictInternalHom.map (modelShiftMap M (-n)).op).app (injectiveModel N))

/-- The actual source-model shift comparison is a homotopy equivalence between K-injective
complexes, and precomposition preserves that equivalence. -/
instance sourceModelShiftMap_isIso (M N : max J O) (n : ℤ) :
    IsIso (sourceModelShiftMap M N n) := by
  apply (DerivedCategory.isIso_Q_map_iff_quasiIso _ _).2
  exact strictInternalHom_quasiIso_precomp
    (modelShiftMap M (-n)) (modelShiftMap_quasiIso M (-n)) (injectiveModel N)

/-- The target-variable derived shift comparison, with all maps fixed by actual cochain
postcomposition, strict shift matrices and derived localization. -/
def targetShiftIso (M N : max J O) (n : ℤ) :
    obj M (N⟦n⟧) ≅ (obj M N)⟦n⟧ :=
  (modelComparisonIso M (N⟦n⟧)).symm ≪≫
    (asIso (targetModelShiftMap M N n)).symm ≪≫
    DerivedCategory.Q.mapIso
      (strictTargetShiftIso (injectiveModel M) (injectiveModel N) n) ≪≫
    (Functor.commShiftIso
      (DerivedCategory.Q : CochainComplex (ringedSiteModuleCategory J O) ℤ ⥤ max J O) n).app
        ((strictInternalHom.obj (op (injectiveModel M))).obj (injectiveModel N)) ≪≫
    (shiftFunctor (max J O) n).mapIso (modelComparisonIso M N)

/-- The source-variable derived shift comparison, using negative source shift and the
coherent sign normalization of the strict cochain Hom. -/
def sourceShiftIso (M N : max J O) (n : ℤ) :
    obj (M⟦-n⟧) N ≅ (obj M N)⟦n⟧ :=
  (modelComparisonIso (M⟦-n⟧) N).symm ≪≫
    asIso (sourceModelShiftMap M N n) ≪≫
    DerivedCategory.Q.mapIso
      (strictSourceShiftIso (injectiveModel M) (injectiveModel N) n) ≪≫
    (Functor.commShiftIso
      (DerivedCategory.Q : CochainComplex (ringedSiteModuleCategory J O) ℤ ⥤ max J O) n).app
        ((strictInternalHom.obj (op (injectiveModel M))).obj (injectiveModel N)) ≪≫
    (shiftFunctor (max J O) n).mapIso (modelComparisonIso M N)

/-- The natural target-variable shift comparison of the actual derived sheaf-Hom functor. -/
def targetCommShiftIso (M : max J O) (n : ℤ) :
    shiftFunctor (max J O) n ⋙ targetFunctor M ≅
      targetFunctor M ⋙ shiftFunctor (max J O) n :=
  NatIso.ofComponents (fun N ↦ targetShiftIso M N n) (by intro N N' f; sorry)

/-- The natural source-variable comparison respects the opposite category's negative shift. -/
def sourceCommShiftIso (N : max J O) (n : ℤ) :
    shiftFunctor (max J O)ᵒᵖ n ⋙ sourceFunctor N ≅
      sourceFunctor N ⋙ shiftFunctor (max J O) n :=
  Functor.isoWhiskerRight
      (Pretriangulated.shiftFunctorOpIso (max J O) n (-n) (add_neg_cancel n))
      (sourceFunctor N) ≪≫
    NatIso.ofComponents (fun M ↦ sourceShiftIso M.unop N n) (by intro M M' f; sorry)

/-- The actual target-variable derived sheaf-Hom functor commutes coherently with shifts. -/
@[stacks 08JC "canonical sheaf-valued target-variable shift compatibility"]
instance targetFunctor_commShift (M : max J O) : (targetFunctor M).CommShift ℤ where
  commShiftIso := targetCommShiftIso M
  commShiftIso_zero := sorry
  commShiftIso_add := sorry

/-- The actual contravariant source-variable derived sheaf-Hom functor commutes with shifts. -/
@[stacks 08JC "canonical sheaf-valued source-variable shift compatibility"]
instance sourceFunctor_commShift (N : max J O) : (sourceFunctor N).CommShift ℤ where
  commShiftIso := sourceCommShiftIso N
  commShiftIso_zero := sorry
  commShiftIso_add := sorry

/-- Termwise split short exact sequences in the target variable induce distinguished
triangles under the actual derived sheaf-Hom construction. -/
@[stacks 08JC "canonical sheaf-valued target-variable triangulated functor"]
instance targetFunctor_isTriangulated (M : max J O) :
    (targetFunctor M).IsTriangulated := sorry

/-- Termwise split short exact sequences in the source variable induce distinguished
triangles under the actual contravariant derived sheaf-Hom construction. -/
@[stacks 08JC "canonical sheaf-valued source-variable triangulated functor"]
instance sourceFunctor_isTriangulated (N : max J O) :
    (sourceFunctor N).IsTriangulated := sorry

end RingedSite.Hom.ModuleDerived.InternalHom
