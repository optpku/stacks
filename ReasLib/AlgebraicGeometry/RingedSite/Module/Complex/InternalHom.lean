/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.Algebra.Category.ModuleCat.Sheaf.RingedSite.InternalHom
public import ReasLib.Algebra.Category.ModuleCat.Sheaf.RingedSite.Tensor.Exact
public import Mathlib.Algebra.Category.ModuleCat.Sheaf.Colimits
public import Mathlib.Algebra.Category.ModuleCat.Sheaf.Limits
public import ReasLib.Algebra.Homology.CochainComplex.Monoidal.Closed
public import Mathlib.Algebra.Homology.HomotopyCategory.KInjective
import ReasLib.Algebra.Category.ModuleCat.Sheaf.RingedSite.FreeFlatCover.Flat
import ReasLib.Algebra.Category.ModuleCat.Sheaf.Localization.DirectSum
import Mathlib.CategoryTheory.Preadditive.Yoneda.Limits
import Mathlib.Algebra.Homology.ShortComplex.Ab
import Mathlib.Algebra.Homology.HomotopyCategory.HomComplexCohomology
public import ReasLib.AlgebraicGeometry.RingedSite.Module.Basic

/-! # Strict internal Hom of complexes of module sheaves

The product-valued cochain internal Hom uses the canonical local-Hom sheaves and
its signed commutator differential.
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits CategoryTheory.MonoidalCategory Opposite
open SheafOfModules.RingedSite

noncomputable section

set_option backward.isDefEq.respectTransparency false

universe u v

namespace RingedSite.Hom.ModuleDerived.InternalHom

section FlatTests

variable {A : Type*} [Category* A] [Abelian A] [MonoidalCategory A]

private lemma acyclic_of_flat_tests
    (cover : ∀ M : A, FlatPresentation M) (H : CochainComplex A ℤ)
    (h : ∀ (B : A), IsFlat B →
      (((preadditiveCoyoneda.obj (op B)).mapHomologicalComplex (.up ℤ)).obj H).Acyclic) :
    H.Acyclic := by
  intro n
  let P := cover (H.cycles n)
  have hP := h P.source P.isFlat n
  rw [HomologicalComplex.exactAt_iff] at hP
  have hz : (P.map ≫ H.iCycles n) ≫ H.d n ((ComplexShape.up ℤ).next n) = 0 := by
    simp only [Category.assoc, HomologicalComplex.iCycles_d, comp_zero]
  obtain ⟨b, hb⟩ := (ShortComplex.ab_exact_iff_ker_le_range).mp hP
    (show P.map ≫ H.iCycles n ∈ _ from hz)
  have hb' : P.map ≫ H.iCycles n =
      b ≫ H.d ((ComplexShape.up ℤ).prev n) n := hb.symm
  have hp : P.map ≫ H.homologyπ n = 0 := by
    have hzero := H.liftCycles_homologyπ_eq_zero_of_boundary
      (P.map ≫ H.iCycles n) _ rfl b hb'
    have he : H.liftCycles (P.map ≫ H.iCycles n) _ rfl hz = P.map := by
      apply (cancel_mono (H.iCycles n)).mp
      simp only [HomologicalComplex.liftCycles_i]
    rw [he] at hzero
    exact hzero
  -- Local instance justification (proof-local temporary data): This particular flat presentation supplies the epimorphism needed for cancellation and the zero-homology criterion.
  haveI := P.epi_map
  have hp' : H.homologyπ n = 0 := by
    apply (cancel_epi P.map).mp
    simpa using hp
  rw [HomologicalComplex.exactAt_iff_isZero_homology]
  exact IsZero.of_epi_eq_zero (H.homologyπ n) hp'

omit [MonoidalCategory A] in
private lemma quasiIso_iff_acyclic_cone {F G : CochainComplex A ℤ} (f : F ⟶ G) :
    QuasiIso f ↔ (CochainComplex.mappingCone f).Acyclic := by
  rw [← HomotopyCategory.quotient_obj_mem_subcategoryAcyclic_iff_acyclic]
  change QuasiIso f ↔ (HomotopyCategory.subcategoryAcyclic A)
    (CochainComplex.mappingCone.triangleh f).obj₃
  rw [← (HomotopyCategory.subcategoryAcyclic A).trW_iff_of_distinguished _
      (HomotopyCategory.mappingCone_triangleh_distinguished f),
    ← HomotopyCategory.quasiIso_eq_trW_subcategoryAcyclic]
  exact (HomotopyCategory.quotient_map_mem_quasiIso_iff f).symm

private lemma quasiIso_of_flat_tests
    (cover : ∀ M : A, FlatPresentation M) {F G : CochainComplex A ℤ} (f : F ⟶ G)
    (h : ∀ (B : A), IsFlat B → QuasiIso
      (((preadditiveCoyoneda.obj (op B)).mapHomologicalComplex (.up ℤ)).map f)) :
    QuasiIso f := by
  rw [quasiIso_iff_acyclic_cone]
  apply acyclic_of_flat_tests cover
  intro B hB n
  exact ((quasiIso_iff_acyclic_cone _).mp (h B hB) n).of_iso
    (CochainComplex.mappingCone.mapHomologicalComplexIso f
      (preadditiveCoyoneda.obj (op B))).symm

omit [MonoidalCategory A] in
private def homComplexPrecomp {F G : CochainComplex A ℤ} (f : F ⟶ G)
    (I : CochainComplex A ℤ) :
    _root_.CochainComplex.HomComplex G I ⟶ _root_.CochainComplex.HomComplex F I where
  f n := AddCommGrpCat.ofHom
    { toFun := fun z ↦ (_root_.CochainComplex.HomComplex.Cochain.ofHom f).comp z (zero_add n)
      map_zero' := by simp
      map_add' := by intros; simp }
  comm' n m h := by
    ext z
    exact (_root_.CochainComplex.HomComplex.δ_ofHom_comp f z m)

omit [MonoidalCategory A] in
private lemma homComplexPrecomp_quasiIso {F G : CochainComplex A ℤ} (f : F ⟶ G)
    (hf : QuasiIso f) (I : CochainComplex A ℤ) [I.IsKInjective] :
    QuasiIso (homComplexPrecomp f I) := by
  rw [quasiIso_iff]
  intro n
  let eF := _root_.CochainComplex.HomComplex.CohomologyClass.homAddEquiv (K := F) (L := I) (n := n)
  let eG := _root_.CochainComplex.HomComplex.CohomologyClass.homAddEquiv (K := G) (L := I) (n := n)
  let qf := (HomotopyCategory.quotient A (.up ℤ)).map f
  let φH : _root_.CochainComplex.HomComplex.CohomologyClass G I n →+
      _root_.CochainComplex.HomComplex.CohomologyClass F I n :=
    { toFun := fun x ↦ eF.symm (qf ≫ eG x)
      map_zero' := by simp
      map_add' := by intros; simp [Preadditive.comp_add] }
  let φK : _root_.CochainComplex.HomComplex.Cocycle G I n →+
      _root_.CochainComplex.HomComplex.Cocycle F I n :=
    { toFun := fun z ↦ z.precomp f
      map_zero' := by ext; simp
      map_add' := by intros; ext; simp }
  let γ : ShortComplex.LeftHomologyMapData
      ((HomologicalComplex.shortComplexFunctor _ (.up ℤ) n).map (homComplexPrecomp f I))
      (_root_.CochainComplex.HomComplex.leftHomologyData G I n)
      (_root_.CochainComplex.HomComplex.leftHomologyData F I n) :=
    { φK := AddCommGrpCat.ofHom φK
      φH := AddCommGrpCat.ofHom φH
      commi := by rfl
      commf' := by
        apply (cancel_mono (_root_.CochainComplex.HomComplex.leftHomologyData F I n).i).mp
        have hc : (_root_.CochainComplex.HomComplex.leftHomologyData G I n).i ≫
            (homComplexPrecomp f I).f n = AddCommGrpCat.ofHom φK ≫
              (_root_.CochainComplex.HomComplex.leftHomologyData F I n).i := rfl
        erw [Category.assoc, ← hc, ← Category.assoc,
          ShortComplex.LeftHomologyData.f'_i, Category.assoc,
          ShortComplex.LeftHomologyData.f'_i]
        exact ((homComplexPrecomp f I).comm _ _).symm
      commπ := by
        ext z
        change eF.symm (qf ≫ eG (_root_.CochainComplex.HomComplex.CohomologyClass.mk z)) =
          _root_.CochainComplex.HomComplex.CohomologyClass.mk (z.precomp f)
        apply eF.injective
        simp only [AddEquiv.apply_symm_apply]
        change qf ≫ _root_.CochainComplex.HomComplex.CohomologyClass.toHom
          (_root_.CochainComplex.HomComplex.CohomologyClass.mk z) =
          _root_.CochainComplex.HomComplex.CohomologyClass.toHom
            (_root_.CochainComplex.HomComplex.CohomologyClass.mk (z.precomp f))
        simp only [_root_.CochainComplex.HomComplex.CohomologyClass.toHom_mk,
          _root_.CochainComplex.HomComplex.Cocycle.equivHomShift_symm_precomp,
          Functor.map_comp]
        rfl }
  have hlocal := _root_.CochainComplex.IsKInjective.rightOrthogonal (I⟦n⟧)
  rw [← ObjectProperty.isLocal_trW] at hlocal
  have hqf : (HomotopyCategory.subcategoryAcyclic A).trW qf := by
    rw [← HomotopyCategory.quasiIso_eq_trW_subcategoryAcyclic]
    exact (HomotopyCategory.quotient_map_mem_quasiIso_iff f).mpr hf
  have hbij : Function.Bijective φH :=
    eF.symm.bijective.comp ((hlocal qf hqf).comp eG.bijective)
  have hφ : IsIso (AddCommGrpCat.ofHom φH) :=
    (ConcreteCategory.isIso_iff_bijective _).mpr hbij
  exact (quasiIsoAt_iff _ n).mpr (γ.quasiIso_iff.mpr hφ)

end FlatTests


section CochainTests

variable {A : Type*} [Category* A] [Abelian A]
variable [MonoidalCategory A] [MonoidalPreadditive A] [MonoidalClosed A]
variable [HasProductsOfShape ℤ A]
variable [∀ X Y : GradedObject ℤ A, GradedObject.HasTensor X Y]
variable [∀ X Y Z : GradedObject ℤ A, GradedObject.HasGoodTensor₁₂Tensor X Y Z]
variable [∀ X Y Z : GradedObject ℤ A, GradedObject.HasGoodTensorTensor₂₃ X Y Z]
variable [∀ X Y Z W : GradedObject ℤ A, GradedObject.HasTensor₄ObjExt X Y Z W]
variable [∀ X, PreservesColimit (Functor.empty.{0} A) ((curriedTensor A).obj X)]
variable [∀ X, PreservesColimit (Functor.empty.{0} A) ((curriedTensor A).flip.obj X)]

open CategoryTheory.CochainComplex.InternalHom

private def asCochain {B : A} (X Y : CochainComplex A ℤ) {n : ℤ}
    (a : B ⟶ gradedObj X Y n) :
    _root_.CochainComplex.HomComplex.Cochain
      (((tensorRight B).mapHomologicalComplex (.up ℤ)).obj X) Y n :=
  _root_.CochainComplex.HomComplex.Cochain.mk fun i j h ↦
    CategoryTheory.MonoidalClosed.uncurry (a ≫ Pi.π (family X Y n) i) ≫
      eqToHom (congrArg Y.X h)

private theorem asCochain_differential {B : A} (X Y : CochainComplex A ℤ) (n : ℤ)
    (a : B ⟶ gradedObj X Y n) :
    asCochain X Y (a ≫ differential X Y n) =
      _root_.CochainComplex.HomComplex.δ n (n + 1) (asCochain X Y a) := by
  apply _root_.CochainComplex.HomComplex.Cochain.ext
  intro i j h
  subst j
  rw [_root_.CochainComplex.HomComplex.δ_v _ _ rfl _ _ _ rfl
    (i + n) (i + 1) (by omega) rfl]
  simp only [asCochain, _root_.CochainComplex.HomComplex.Cochain.mk_v,
    eqToHom_refl, Category.comp_id, differential, Category.assoc, Pi.lift_π]
  simp only [Preadditive.comp_add, Linear.comp_units_smul]
  change ((ihom.adjunction (X.X i)).homAddEquiv B _).symm _ = _
  rw [map_add, Units.smul_def, map_zsmul]
  change CategoryTheory.MonoidalClosed.uncurry (a ≫ postDifferential X Y n i) +
    (n + 1).negOnePow • CategoryTheory.MonoidalClosed.uncurry
      (a ≫ preDifferential X Y n i) = _
  congr 1
  · simp only [postDifferential, Category.assoc]
    rw [← eqToHom_map (ihom (X.X i)) (congrArg Y.X (postDegree i n)),
      ← Functor.map_comp, ← Category.assoc,
      CategoryTheory.MonoidalClosed.uncurry_natural_right,
      HomologicalComplex.d_comp_eqToHom]
    all_goals simp only [ComplexShape.up_Rel, add_assoc]
  · congr 1
    simp only [preDifferential, ← CategoryTheory.MonoidalClosed.curry_natural_left,
      CategoryTheory.MonoidalClosed.uncurry_curry,
      CategoryTheory.MonoidalClosed.uncurry_eq, Category.assoc,
      MonoidalCategory.whiskerLeft_comp]
    rw [MonoidalCategory.whisker_exchange_assoc]
    rw [CategoryTheory.MonoidalClosed.whiskerLeft_curry_ihom_ev_app]
    rfl

private def asCochainEquiv (B : A) (F I : CochainComplex A ℤ) (n : ℤ) :
    (B ⟶ gradedObj F I n) ≃+
      _root_.CochainComplex.HomComplex.Cochain
        (((tensorRight B).mapHomologicalComplex (.up ℤ)).obj F) I n where
  toFun := asCochain F I
  invFun z := Pi.lift fun i ↦ MonoidalClosed.curry (z.v i (i + n) rfl)
  left_inv a := by
    apply Pi.hom_ext
    intro i
    simp only [Pi.lift_π, asCochain, _root_.CochainComplex.HomComplex.Cochain.mk_v,
      eqToHom_refl, Category.comp_id, MonoidalClosed.curry_uncurry]
  right_inv z := by
    apply _root_.CochainComplex.HomComplex.Cochain.ext
    intro i j h
    subst j
    simp only [asCochain, _root_.CochainComplex.HomComplex.Cochain.mk_v,
      Pi.lift_π, eqToHom_refl, Category.comp_id, MonoidalClosed.uncurry_curry]
  map_add' a b := by
    apply _root_.CochainComplex.HomComplex.Cochain.ext
    intro i j h
    subst j
    simp only [asCochain, _root_.CochainComplex.HomComplex.Cochain.mk_v,
      eqToHom_refl, Category.comp_id, Preadditive.add_comp,
      _root_.CochainComplex.HomComplex.Cochain.add_v]
    exact ((ihom.adjunction (F.X i)).homAddEquiv B _).symm.map_add _ _

private def homTestIso (B : A) (F I : CochainComplex A ℤ) :
    ((preadditiveCoyoneda.obj (op B)).mapHomologicalComplex (.up ℤ)).obj
        (CategoryTheory.CochainComplex.InternalHom.obj F I) ≅
      _root_.CochainComplex.HomComplex
        (((tensorRight B).mapHomologicalComplex (.up ℤ)).obj F) I :=
  HomologicalComplex.Hom.isoOfComponents
    (fun n ↦ (asCochainEquiv B F I n).toAddCommGrpIso) (by
      intro n m h
      obtain rfl : n + 1 = m := h
      ext a
      change _root_.CochainComplex.HomComplex.δ n (n + 1) (asCochain F I a) =
        asCochain F I (a ≫ (obj F I).d n (n + 1))
      simpa only [obj, CochainComplex.of_d] using (asCochain_differential F I n a).symm)

private def canonicalPrecomp {F G : CochainComplex A ℤ} (f : F ⟶ G)
    (I : CochainComplex A ℤ) : obj G I ⟶ obj F I :=
  curry (HomologicalComplex.tensorHom f (𝟙 (obj G I)) ≫ uncurry (𝟙 (obj G I)))

private theorem curry_units_smul {X B D : A} (r : ℤˣ) (f : X ⊗ B ⟶ D) :
    CategoryTheory.MonoidalClosed.curry (r • f) =
      r • CategoryTheory.MonoidalClosed.curry f := by
  change (ihom.adjunction X).homAddEquiv B D ((r : ℤ) • f) =
    (r : ℤ) • (ihom.adjunction X).homAddEquiv B D f
  exact map_zsmul _ _ _

private lemma canonicalPrecomp_f_π {F G : CochainComplex A ℤ} (f : F ⟶ G)
    (I : CochainComplex A ℤ) (i n : ℤ) :
    (canonicalPrecomp f I).f n ≫ Pi.π (family F I n) i =
      MonoidalClosed.curry
        ((f.f i ▷ gradedObj G I n) ≫
          MonoidalClosed.uncurry (Pi.π (family G I n) i)) := by
  rw [canonicalPrecomp, curry_f_π]
  simp only [HomologicalComplex.comp_f, Category.assoc]
  change (i * n).negOnePow • MonoidalClosed.curry
    (GradedObject.Monoidal.ιTensorObj F.X (obj G I).X i n (i + n) rfl ≫
      GradedObject.Monoidal.tensorHom f.f (𝟙 (obj G I) : obj G I ⟶ obj G I).f (i + n) ≫
        (uncurry (𝟙 (obj G I))).f (i + n)) = _
  rw [GradedObject.Monoidal.ι_tensorHom_assoc]
  simp only [HomologicalComplex.id_f, tensorHom_id]
  change (i * n).negOnePow • MonoidalClosed.curry
    (f.f i ▷ gradedObj G I n ≫
      HomologicalComplex.ιTensorObj G (obj G I) i n (i + n) rfl ≫
        (uncurry (𝟙 (obj G I))).f (i + n)) = _
  rw [ιTensorObj_uncurry_f]
  simp only [HomologicalComplex.id_f, MonoidalCategory.whiskerLeft_id, Category.id_comp,
    eqToHom_refl, Category.comp_id, Linear.comp_units_smul,
    curry_units_smul, smul_smul, Int.units_mul_self, one_smul,
    MonoidalClosed.uncurry_eq, Category.assoc]

private lemma homTestIso_naturality (B : A) {F G : CochainComplex A ℤ}
    (f : F ⟶ G) (I : CochainComplex A ℤ) :
    ((preadditiveCoyoneda.obj (op B)).mapHomologicalComplex (.up ℤ)).map
        (canonicalPrecomp f I) ≫ (homTestIso B F I).hom =
      (homTestIso B G I).hom ≫
        homComplexPrecomp (((tensorRight B).mapHomologicalComplex (.up ℤ)).map f) I := by
  ext n a
  apply _root_.CochainComplex.HomComplex.Cochain.ext
  intro i j h
  subst j
  change (asCochain F I (a ≫ (canonicalPrecomp f I).f n)).v i (i + n) rfl =
    ((_root_.CochainComplex.HomComplex.Cochain.ofHom
      (((tensorRight B).mapHomologicalComplex (.up ℤ)).map f)).comp
        (asCochain G I a) (zero_add n)).v i (i + n) rfl
  simp only [asCochain, _root_.CochainComplex.HomComplex.Cochain.mk_v,
    Category.assoc, canonicalPrecomp_f_π, eqToHom_refl, Category.comp_id,
    MonoidalClosed.uncurry_natural_left, MonoidalClosed.uncurry_curry]
  rw [_root_.CochainComplex.HomComplex.Cochain.zero_cochain_comp_v]
  simp only [_root_.CochainComplex.HomComplex.Cochain.ofHom_v,
    asCochain, _root_.CochainComplex.HomComplex.Cochain.mk_v,
    eqToHom_refl, Category.comp_id, MonoidalClosed.uncurry_natural_left,
    Functor.mapHomologicalComplex_map_f]
  exact MonoidalCategory.whisker_exchange_assoc _ _ _

private lemma canonicalPrecomp_quasiIso
    (cover : ∀ M : A, FlatPresentation M) {F G : CochainComplex A ℤ}
    (f : F ⟶ G) (hf : QuasiIso f) (I : CochainComplex A ℤ) [I.IsKInjective] :
    QuasiIso (canonicalPrecomp f I) := by
  apply quasiIso_of_flat_tests cover
  intro B hB
  -- Local instance justification (proof-local temporary data): Exact tensoring uses the supplied flatness of this particular test object.
  haveI := hB
  -- Local instance justification (proof-local temporary data): The native homology-preservation theorem consumes the supplied quasi-isomorphism of this particular arrow.
  haveI := hf
  have ht : QuasiIso (((tensorRight B).mapHomologicalComplex (.up ℤ)).map f) :=
    HomologicalComplex.quasiIso_map_of_preservesHomology f (tensorRight B)
  exact (quasiIso_iff_of_arrow_mk_iso _ _
    (Arrow.isoMk (homTestIso B G I) (homTestIso B F I)
      (homTestIso_naturality B f I).symm)).mpr
      (homComplexPrecomp_quasiIso
        (((tensorRight B).mapHomologicalComplex (.up ℤ)).map f) ht I)

end CochainTests

variable {C : Type u} [Category.{v} C] {J : GrothendieckTopology C}
variable [J.HasSheafCompose (forget₂ CommRingCat.{max u v} RingCat.{max u v})]
variable [HasWeakSheafify J AddCommGrpCat.{max u v}]
variable [J.WEqualsLocallyBijective AddCommGrpCat.{max u v}]
variable {O : Sheaf J CommRingCat.{max u v}}

/-- The actual product-valued cochain internal-Hom bifunctor on module sheaves. -/
def strictInternalHom :
    (CochainComplex (ringedSiteModuleCategory J O) ℤ)ᵒᵖ ⥤
      CochainComplex (ringedSiteModuleCategory J O) ℤ ⥤
        CochainComplex (ringedSiteModuleCategory J O) ℤ := by
  let tensorExists : ∀ X Y : GradedObject ℤ (ringedSiteModuleCategory J O),
      GradedObject.HasTensor X Y :=
    fun _ _ _ ↦ HasColimitsOfShape.has_colimit _
  let goodLeft : ∀ X Y Z : GradedObject ℤ (ringedSiteModuleCategory J O),
      GradedObject.HasGoodTensor₁₂Tensor X Y Z :=
    fun _ _ _ _ _ ↦ PreservesColimitsOfShape.preservesColimit
  let goodRight : ∀ X Y Z : GradedObject ℤ (ringedSiteModuleCategory J O),
      GradedObject.HasGoodTensorTensor₂₃ X Y Z :=
    fun _ _ _ _ _ ↦ PreservesColimitsOfShape.preservesColimit
  let tensorExt : ∀ X Y Z W : GradedObject ℤ (ringedSiteModuleCategory J O),
      GradedObject.HasTensor₄ObjExt X Y Z W :=
    fun _ _ _ _ _ _ ↦ PreservesColimitsOfShape.preservesColimit
  let preservesLeft : ∀ X, PreservesColimit (Functor.empty.{0} (ringedSiteModuleCategory J O))
      ((curriedTensor (ringedSiteModuleCategory J O)).obj X) :=
    fun _ ↦ PreservesColimitsOfShape.preservesColimit
  let preservesRight : ∀ X, PreservesColimit (Functor.empty.{0} (ringedSiteModuleCategory J O))
      ((curriedTensor (ringedSiteModuleCategory J O)).flip.obj X) :=
    fun _ ↦ PreservesColimitsOfShape.preservesColimit
  let closed := @CochainComplex.InternalHom.monoidalClosed
    (ringedSiteModuleCategory J O)
    inferInstance inferInstance inferInstance inferInstance inferInstance
    inferInstance inferInstance tensorExists goodLeft goodRight tensorExt
    preservesLeft preservesRight
  exact @MonoidalClosed.internalHom _ inferInstance _ closed

set_option maxHeartbeats 2000000 in
/-- Precomposition by a quasi-isomorphism induces a quasi-isomorphism of strict
internal-Hom complexes when the target is K-injective. -/
theorem strictInternalHom_quasiIso_precomp
    {F G : CochainComplex (ringedSiteModuleCategory.{u, v, max u v, max u v} J O) ℤ}
    (f : F ⟶ G) (hf : QuasiIso f)
    (I : CochainComplex (ringedSiteModuleCategory.{u, v, max u v, max u v} J O) ℤ) [I.IsKInjective] :
    QuasiIso ((strictInternalHom.map f.op).app I) := by
  -- Local instance justification (defeq pin): Select the identical tensor-colimit certificate used in strictInternalHom so that its adjunction computes definitionally.
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
  -- Local instance justification (defeq pin): Native precomposition and uncurrying must compute with exactly the explicit signed closed structure defining strictInternalHom.
  letI closed := @CochainComplex.InternalHom.monoidalClosed
    (ringedSiteModuleCategory J O)
    inferInstance inferInstance inferInstance inferInstance inferInstance
    inferInstance inferInstance tensorExists goodLeft goodRight tensorExt
    preservesLeft preservesRight
  -- Local instance justification (proof-local temporary data): The canonical direct-sum slice adjunctions are supplied only to invoke the flat-presentation construction.
  haveI : SheafOfModules.Localization.HasLowerShriek.{max u v} (ringSheaf J O) :=
    { isRightAdjoint U :=
        (SheafOfModules.Localization.lowerShriekDirectSumAdjunction (ringSheaf J O) U).isRightAdjoint }
  change QuasiIso ((MonoidalClosed.pre f).app I)
  have hu (X Z Y : CochainComplex (ringedSiteModuleCategory J O) ℤ)
      (g : Z ⟶ CochainComplex.InternalHom.obj X Y) :
      MonoidalClosed.uncurry g = CochainComplex.InternalHom.uncurry g := by
    change ((Adjunction.mkOfHomEquiv
      (CochainComplex.InternalHom.coreHomEquiv X)).homEquiv Z Y).symm g = _
    rw [Adjunction.mkOfHomEquiv_homEquiv]
    rfl
  have he : (MonoidalClosed.pre f).app I = canonicalPrecomp f I := by
    apply MonoidalClosed.uncurry_injective
    rw [MonoidalClosed.uncurry_pre]
    rw [hu, ← MonoidalClosed.uncurry_id_eq_ev, hu]
    change _ = CochainComplex.InternalHom.uncurry
      (CochainComplex.InternalHom.curry
        (HomologicalComplex.tensorHom f (𝟙 (CochainComplex.InternalHom.obj G I)) ≫
          CochainComplex.InternalHom.uncurry (𝟙 (CochainComplex.InternalHom.obj G I))))
    exact ((CochainComplex.InternalHom.homEquiv F
      (CochainComplex.InternalHom.obj G I) I).left_inv _).symm
  rw [he]
  exact canonicalPrecomp_quasiIso
    (fun M ↦ SheafOfModules.RingedSite.FreeFlatCover.presentation M) f hf I

end RingedSite.Hom.ModuleDerived.InternalHom
