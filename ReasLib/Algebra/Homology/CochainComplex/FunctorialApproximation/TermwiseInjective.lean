/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import Mathlib.CategoryTheory.Abelian.GrothendieckCategory.Basic
public import Mathlib.Tactic.CrossRefAttribute
public import ReasLib.Algebra.Homology.CochainComplex.FunctorialApproximation
public import ReasLib.CategoryTheory.Subobject.Injective
public import ReasLib.CategoryTheory.Abelian.FunctorialInjectives.Grothendieck
public import Mathlib.Algebra.Homology.HomotopyCategory.MappingCocone
public import Mathlib.Algebra.Homology.HomologicalComplexAbelian
public import Mathlib.Algebra.Homology.HomologySequence

@[expose] public section

/-!
# Functorial Complex Approximations with Injective Factors

This module refines a functorial cochain-complex approximation by choosing, in every degree, a
concrete factorization of its comparison map through an injective subobject of the target term.
The refinement is neutral: its data make sense without a Grothendieck hypothesis, while the
Grothendieck assumption appears only in the existence theorem.
-/

open CategoryTheory Limits

universe w v u

namespace CochainComplex

namespace FunctorialComplexApproximation

/-- A functorial complex approximation equipped degreewise with concrete factorizations of its
comparison maps through injective subobjects. -/
@[stacks 079N "functorial approximation with injective factors"]
structure WithInjectiveFactors (C : Type u) [Category.{v} C] [HasZeroMorphisms C]
    [CategoryWithHomology C] extends toApproximation : FunctorialComplexApproximation C where
  /-- The chosen injective-subobject factorization in degree `n` at the complex `M`. -/
  factor (M : CochainComplex C ℤ) (n : ℤ) :
    Subobject.InjectiveFactor ((toApproximation.ι.app M).f n)

namespace WithInjectiveFactors

section Neutral

variable {C : Type u} [Category.{v} C] [HasZeroMorphisms C] [CategoryWithHomology C]

/-- The chosen injective subobject containing the degree-`n` comparison map at `M`. -/
abbrev injectiveSubobject (J : WithInjectiveFactors C) (M : CochainComplex C ℤ) (n : ℤ) :
    Subobject ((J.toFunctor.obj M).X n) :=
  (J.factor M n).subobject

/-- The concrete factor map into the chosen injective subobject. -/
abbrev factorThru (J : WithInjectiveFactors C) (M : CochainComplex C ℤ) (n : ℤ) :
    M.X n ⟶ J.injectiveSubobject M n :=
  (J.factor M n).lift

/-- The chosen factor map recovers the corresponding component of the comparison map. -/
@[reassoc (attr := simp)]
theorem factorThru_arrow (J : WithInjectiveFactors C) (M : CochainComplex C ℤ) (n : ℤ) :
    J.factorThru M n ≫ (J.injectiveSubobject M n).arrow = (J.ι.app M).f n :=
  (J.factor M n).lift_arrow

/-- The comparison component belongs to the chosen injective subobject. -/
theorem factors (J : WithInjectiveFactors C) (M : CochainComplex C ℤ) (n : ℤ) :
    (J.injectiveSubobject M n).Factors ((J.ι.app M).f n) :=
  (Subobject.factors_iff _ _).mpr ⟨J.factorThru M n, J.factorThru_arrow M n⟩

/-- The inherited monomorphism proof for the comparison transformation is available to
typeclass search. -/
instance comparisonMono (J : WithInjectiveFactors C) : Mono J.ι :=
  J.toApproximation.mono_ι

/-- The inherited quasi-isomorphism proof for each comparison component is available to
typeclass search. -/
instance comparisonQuasiIso (J : WithInjectiveFactors C) (M : CochainComplex C ℤ) :
    QuasiIso (J.ι.app M) :=
  J.quasiIso_app M

section FiniteLimits

variable [HasFiniteLimits C]

/-- The comparison map is a monomorphism in each degree. -/
instance mono_f (J : WithInjectiveFactors C) (M : CochainComplex C ℤ) (n : ℤ) :
    Mono ((J.ι.app M).f n) := inferInstance

end FiniteLimits

end Neutral

section Construction


variable {C : Type u} [Category.{v} C] [Abelian C] [HasFunctorialInjectives C]

/-- The source's two-term contractible arrangement of the supplied injective targets. -/
noncomputable def injectiveComplex (M : CochainComplex C ℤ) : CochainComplex C ℤ :=
  CochainComplex.of
    (fun n ↦ HasFunctorialInjectives.obj (M.X n) ⊞ HasFunctorialInjectives.obj (M.X (n + 1)))
    (fun _ ↦ biprod.snd ≫ biprod.inl)
    (fun _ ↦ by simp)

/-- A complex map acts on the two injective targets by the given injective functor. -/
noncomputable def injectiveComplexMap {M N : CochainComplex C ℤ} (f : M ⟶ N) :
    injectiveComplex M ⟶ injectiveComplex N :=
  CochainComplex.ofHom
    (fun n ↦ biprod.map (HasFunctorialInjectives.map (f.f n))
      (HasFunctorialInjectives.map (f.f (n + 1)))) (by
        intro n
        simp only [injectiveComplex, CochainComplex.of_d, biprod.map_snd_assoc,
          biprod.inl_map, Category.assoc])

/-- The map into the contractible arrangement uses the original embedding and its next differential. -/
noncomputable def injectiveComparison (M : CochainComplex C ℤ) : M ⟶ injectiveComplex M :=
  CochainComplex.ofHom
    (fun n ↦ biprod.lift (HasFunctorialInjectives.ι.app (M.X n))
      (M.d n (n + 1) ≫ HasFunctorialInjectives.ι.app (M.X (n + 1)))) (by
        intro n
        apply biprod.hom_ext
        · simp only [injectiveComplex, CochainComplex.of_d, Category.assoc,
            biprod.inl_fst, Category.comp_id, biprod.lift_snd_assoc, biprod.lift_fst]
        · simp only [injectiveComplex, CochainComplex.of_d, Category.assoc,
            biprod.inl_snd, comp_zero, biprod.lift_snd, M.d_comp_d_assoc, zero_comp])

set_option backward.isDefEq.respectTransparency false in
/-- Naturality of the specified two-component embedding. -/
theorem injectiveComparison_naturality {M N : CochainComplex C ℤ} (f : M ⟶ N) :
    injectiveComparison M ≫ injectiveComplexMap f = f ≫ injectiveComparison N := by
  apply HomologicalComplex.hom_ext
  intro n
  apply biprod.hom_ext
  · dsimp only [HomologicalComplex.comp_f, injectiveComparison, injectiveComplexMap]
    simpa only [Category.assoc, biprod.map_fst, biprod.lift_fst_assoc, biprod.lift_fst,
      HasFunctorialInjectives.map, Functor.id_map] using
      ((HasFunctorialInjectives.ι (C := C)).naturality (f.f n)).symm
  · dsimp only [HomologicalComplex.comp_f, injectiveComparison, injectiveComplexMap]
    simp only [Category.assoc, biprod.map_snd, biprod.lift_snd_assoc, biprod.lift_snd,
      HasFunctorialInjectives.map, ← NatTrans.naturality, Functor.id_map]
    exact (f.comm_assoc n (n + 1) _).symm

set_option backward.isDefEq.respectTransparency false in
private theorem injectiveComparison_mono (M : CochainComplex C ℤ) :
    Mono (injectiveComparison M) := by
  apply HomologicalComplex.mono_of_mono_f
  intro n
  letI := HasFunctorialInjectives.mono_app (C := C) (M.X n)
  exact mono_of_mono_fac (biprod.lift_fst
    (HasFunctorialInjectives.ι.app (M.X n))
    (M.d n (n + 1) ≫ HasFunctorialInjectives.ι.app (M.X (n + 1))))

/-- The actual cokernel complex of the specified embedding. -/
noncomputable abbrev quotientComplex (M : CochainComplex C ℤ) : CochainComplex C ℤ :=
  cokernel (injectiveComparison M)

/-- The induced map of cokernel complexes comes from the actual commuting square. -/
noncomputable def quotientComplexMap {M N : CochainComplex C ℤ} (f : M ⟶ N) :
    quotientComplex M ⟶ quotientComplex N :=
  cokernel.map (injectiveComparison M) (injectiveComparison N) f
    (injectiveComplexMap f) (injectiveComparison_naturality f)

set_option backward.isDefEq.respectTransparency false in
private theorem injectiveComplexMap_id (M : CochainComplex C ℤ) :
    injectiveComplexMap (𝟙 M) = 𝟙 _ := by
  apply HomologicalComplex.hom_ext
  intro n
  apply biprod.hom_ext
  · simp [injectiveComplexMap, HasFunctorialInjectives.map]
  · simp [injectiveComplexMap, HasFunctorialInjectives.map]

set_option backward.isDefEq.respectTransparency false in
private theorem injectiveComplexMap_comp {M N P : CochainComplex C ℤ}
    (f : M ⟶ N) (g : N ⟶ P) :
    injectiveComplexMap (f ≫ g) = injectiveComplexMap f ≫ injectiveComplexMap g := by
  apply HomologicalComplex.hom_ext
  intro n
  apply biprod.hom_ext
  · simp [injectiveComplexMap, HasFunctorialInjectives.map, Category.assoc]
  · simp [injectiveComplexMap, HasFunctorialInjectives.map, Category.assoc]

set_option backward.isDefEq.respectTransparency false in
private theorem quotientComplexMap_id (M : CochainComplex C ℤ) :
    quotientComplexMap (𝟙 M) = 𝟙 _ := by
  apply (cancel_epi (cokernel.π (injectiveComparison M))).1
  simp only [quotientComplexMap, cokernel.map, injectiveComplexMap_id, coequalizer_as_cokernel,
    Category.id_comp, IsColimit.desc_self, Category.comp_id]
  exact Category.comp_id _

set_option backward.isDefEq.respectTransparency false in
private theorem quotientComplexMap_comp {M N P : CochainComplex C ℤ}
    (f : M ⟶ N) (g : N ⟶ P) :
    quotientComplexMap (f ≫ g) = quotientComplexMap f ≫ quotientComplexMap g := by
  apply (cancel_epi (cokernel.π (injectiveComparison M))).1
  simp [quotientComplexMap, cokernel.map, injectiveComplexMap_comp, Category.assoc]

/-- The shifted cone of the actual cokernel map is the source's approximation. -/
noncomputable def approximationComplex (M : CochainComplex C ℤ) : CochainComplex C ℤ :=
  mappingCocone (cokernel.π (injectiveComparison M))

omit [HasFunctorialInjectives C] in
private theorem mappingCocone_ext {K L : CochainComplex C ℤ} (φ : K ⟶ L)
    {A : C} {n : ℤ} {f g : A ⟶ (mappingCocone φ).X n}
    (hfst : f ≫ (mappingCocone.fst φ).f n = g ≫ (mappingCocone.fst φ).f n)
    (hsnd : f ≫ (mappingCocone.snd φ).v n (n + -1) rfl =
      g ≫ (mappingCocone.snd φ).v n (n + -1) rfl) : f = g := by
  calc
    f = f ≫ 𝟙 _ := by rw [Category.comp_id]
    _ = f ≫ ((mappingCocone.fst φ).f n ≫ (mappingCocone.inl φ).v n n (add_zero n) +
        (mappingCocone.snd φ).v n (n + -1) rfl ≫
          (mappingCocone.inr φ).1.v (n + -1) n (by omega)) := by
      rw [mappingCocone.id_X φ n (n + -1) rfl]
    _ = g ≫ ((mappingCocone.fst φ).f n ≫ (mappingCocone.inl φ).v n n (add_zero n) +
        (mappingCocone.snd φ).v n (n + -1) rfl ≫
          (mappingCocone.inr φ).1.v (n + -1) n (by omega)) := by
      simp only [Preadditive.comp_add, ← Category.assoc, hfst, hsnd]
    _ = g := by rw [mappingCocone.id_X φ n (n + -1) rfl, Category.comp_id]

set_option backward.isDefEq.respectTransparency false in
omit [HasFunctorialInjectives C] in
private theorem mappingCocone_δ_snd {K L : CochainComplex C ℤ} (φ : K ⟶ L) :
    HomComplex.δ (-1) 0 (mappingCocone.snd φ) =
      -HomComplex.Cochain.ofHom (mappingCocone.fst φ ≫ φ) := by
  dsimp only [mappingCocone.snd, mappingCocone.fst]
  rw [HomComplex.Cochain.δ_leftShift _ (-1) (-1) 0 (zero_add _) 1 (add_neg_cancel 1)]
  simp only [mappingCone.δ_snd, HomComplex.Cochain.leftShift_neg,
    HomComplex.Cochain.leftShift_comp_zero_cochain, Int.negOnePow_neg, Int.negOnePow_one,
    Units.neg_smul, one_smul, neg_neg, Preadditive.neg_comp, HomComplex.Cochain.ofHom_neg,
    HomComplex.Cochain.ofHom_comp, HomComplex.Cocycle.cochain_ofHom_homOf_eq_coe,
    HomComplex.Cocycle.leftShift_coe]

set_option backward.isDefEq.respectTransparency false in
omit [HasFunctorialInjectives C] in
private theorem mappingCocone_ext_from {K L : CochainComplex C ℤ} (φ : K ⟶ L)
    {A : C} {n : ℤ} {f g : (mappingCocone φ).X n ⟶ A}
    (hinl : (mappingCocone.inl φ).v n n (add_zero n) ≫ f =
      (mappingCocone.inl φ).v n n (add_zero n) ≫ g)
    (hinr : (mappingCocone.inr φ).1.v (n + -1) n (by omega) ≫ f =
      (mappingCocone.inr φ).1.v (n + -1) n (by omega) ≫ g) : f = g := by
  rw [← Category.id_comp f, ← Category.id_comp g,
    ← mappingCocone.id_X φ n (n + -1) rfl]
  simp only [Preadditive.add_comp, Category.assoc, hinl, hinr]

set_option backward.isDefEq.respectTransparency false in
omit [HasFunctorialInjectives C] in
private theorem quasiIso_mappingCocone_lift {M J : CochainComplex C ℤ} (u : M ⟶ J) [Mono u] :
    QuasiIso (mappingCocone.lift (cokernel.π u) u 0 (by simp)) := by
  let Q := cokernel u
  let p : J ⟶ Q := cokernel.π u
  let i : M ⟶ mappingCocone p := mappingCocone.lift p u 0 (by simp [p])
  change QuasiIso i
  -- The quotient is the mapping cocone of the identity of the cokernel.
  let r : mappingCocone p ⟶ mappingCocone (𝟙 Q) :=
    mappingCocone.lift (𝟙 Q) (mappingCocone.fst p ≫ p) (mappingCocone.snd p) (by
      rw [mappingCocone_δ_snd]
      simp)
  have hinl (n : ℤ) : (mappingCocone.inl p).v n n (add_zero n) ≫ r.f n =
      p.f n ≫ (mappingCocone.inl (𝟙 Q)).v n n (add_zero n) := by
    apply mappingCocone_ext (𝟙 Q)
    · simp [r, Category.assoc]
    · simp [r, Category.assoc]
  have hinr (n : ℤ) : (mappingCocone.inr p).1.v (n + -1) n (by omega) ≫ r.f n =
      (mappingCocone.inr (𝟙 Q)).1.v (n + -1) n (by omega) := by
    apply mappingCocone_ext (𝟙 Q)
    · simp [r, Category.assoc]
    · simp [r, Category.assoc]
  have hir : i ≫ r = 0 := by
    apply HomologicalComplex.hom_ext
    intro n
    apply mappingCocone_ext (𝟙 Q)
    · simp [i, r, p, Category.assoc, ← HomologicalComplex.comp_f]
    · simp [i, r, Category.assoc]
  let S := ShortComplex.mk i r hir
  have hS : S.ShortExact := by
    apply HomologicalComplex.shortExact_of_degreewise_shortExact
    intro n
    refine { exact := ?_, mono_f := ?_, epi_g := ?_ }
    · rw [ShortComplex.exact_iff_exact_up_to_refinements]
      intro A z hz
      have hfst : (z ≫ (mappingCocone.fst p).f n) ≫ p.f n = 0 := by
        simpa [S, r, Category.assoc] using
          congrArg (fun k ↦ k ≫ (mappingCocone.fst (𝟙 Q)).f n) hz
      have hsnd : z ≫ (mappingCocone.snd p).v n (n + -1) rfl = 0 := by
        simpa [S, r, Category.assoc] using
          congrArg (fun k ↦ k ≫ (mappingCocone.snd (𝟙 Q)).v n (n + -1) rfl) hz
      let S₀ := ShortComplex.mk u p (by simp [p])
      have he : (S₀.map (HomologicalComplex.eval C (.up ℤ) n)).Exact :=
        (ShortComplex.exact_cokernel u).map _
      letI : Mono (S₀.map (HomologicalComplex.eval C (.up ℤ) n)).f := by
        change Mono (u.f n)
        infer_instance
      obtain ⟨w, hw⟩ := he.lift' (z ≫ (mappingCocone.fst p).f n) hfst
      change w ≫ u.f n = z ≫ (mappingCocone.fst p).f n at hw
      refine ⟨A, 𝟙 A, inferInstance, w, ?_⟩
      apply mappingCocone_ext p
      · simpa [S, i, Category.assoc] using hw.symm
      · simp [S, i, Category.assoc, hsnd]
    · exact mono_of_mono_fac (mappingCocone.lift_f_fst_f p u 0 (by simp [p]) n)
    · constructor
      intro A f g hfg
      change r.f n ≫ f = r.f n ≫ g at hfg
      apply mappingCocone_ext_from (𝟙 Q)
      · apply (cancel_epi (p.f n)).1
        simpa only [← Category.assoc, ← hinl n] using
          congrArg (fun k ↦ (mappingCocone.inl p).v n n (add_zero n) ≫ k) hfg
      · simpa only [← Category.assoc, hinr n] using
          congrArg (fun k ↦ (mappingCocone.inr p).1.v (n + -1) n (by omega) ≫ k) hfg
  -- Its contraction makes both adjacent terms of the homology sequence zero.
  have hT (n : ℤ) : IsZero ((mappingCocone (𝟙 Q)).homology n) := by
    apply (IsZero.iff_id_eq_zero _).2
    have h := ((mappingCone.homotopyToZeroOfId Q).shift (-1)).homologyMap_eq n
    simpa [mappingCocone] using h
  refine ⟨fun n ↦ ?_⟩
  rw [quasiIsoAt_iff_isIso_homologyMap]
  letI : Mono (HomologicalComplex.homologyMap i n) :=
    (hS.homology_exact₁ (n - 1) n (by simp)).mono_g ((hT (n - 1)).eq_of_src _ _)
  letI : Epi (HomologicalComplex.homologyMap i n) :=
    (hS.homology_exact₂ n).epi_f ((hT n).eq_of_tgt _ _)
  exact isIso_of_mono_of_epi _

set_option backward.isDefEq.respectTransparency false in
/-- A map of the specified cokernel arrows acts on their actual mapping cocones. -/
noncomputable def approximationMap {M N : CochainComplex C ℤ} (f : M ⟶ N) :
    approximationComplex M ⟶ approximationComplex N :=
  mappingCocone.lift (cokernel.π (injectiveComparison N))
    (mappingCocone.fst (cokernel.π (injectiveComparison M)) ≫ injectiveComplexMap f)
    ((mappingCocone.snd (cokernel.π (injectiveComparison M))).comp
      (HomComplex.Cochain.ofHom (quotientComplexMap f)) (add_zero (-1))) (by
        rw [HomComplex.δ_comp_ofHom, mappingCocone_δ_snd]
        simp only [HomComplex.Cochain.neg_comp, ← HomComplex.Cochain.ofHom_comp]
        simp only [Category.assoc, quotientComplexMap, cokernel.map, cokernel.π_desc,
          neg_add_cancel])

set_option backward.isDefEq.respectTransparency false in
/-- The actual mapping-cocone construction is functorial. -/
noncomputable def approximationFunctor : CochainComplex C ℤ ⥤ CochainComplex C ℤ where
  obj := approximationComplex
  map := approximationMap
  map_id M := by
    apply HomologicalComplex.hom_ext
    intro n
    apply mappingCocone_ext (cokernel.π (injectiveComparison M))
    · simp [approximationMap, injectiveComplexMap_id]
    · simp [approximationMap, quotientComplexMap_id]
  map_comp f g := by
    apply HomologicalComplex.hom_ext
    intro n
    apply mappingCocone_ext _
    · simp [approximationMap, injectiveComplexMap_comp, Category.assoc]
    · simp [approximationMap, HomComplex.Cochain.comp_zero_cochain_v,
        quotientComplexMap_comp, Category.assoc]

set_option backward.isDefEq.respectTransparency false in
/-- The comparison is the native cocone lift of the embedding, whose cokernel composite vanishes. -/
noncomputable def approximationComparison : 𝟭 (CochainComplex C ℤ) ⟶ approximationFunctor where
  app M := mappingCocone.lift (cokernel.π (injectiveComparison M))
    (injectiveComparison M) 0 (by
      simp only [HomComplex.δ_zero, cokernel.condition, HomComplex.Cochain.ofHom_zero, add_zero])
  naturality M N f := by
    apply HomologicalComplex.hom_ext
    intro n
    apply mappingCocone_ext (cokernel.π (injectiveComparison N))
    · simpa [approximationFunctor, approximationMap, Category.assoc] using
        (congrArg (fun g ↦ g.f n) (injectiveComparison_naturality f)).symm
    · simp [approximationFunctor, approximationMap, Category.assoc,
        HomComplex.Cochain.comp_zero_cochain_v]

set_option backward.isDefEq.respectTransparency false in
/-- Projection of the actual approximation comparison recovers the original two-component embedding. -/
@[reassoc (attr := simp)]
theorem approximationComparison_fst (M : CochainComplex C ℤ) :
    approximationComparison.app M ≫ mappingCocone.fst (cokernel.π (injectiveComparison M)) =
      injectiveComparison M := by
  dsimp only [approximationComparison]
  simp only [mappingCocone.lift_fst]

set_option backward.isDefEq.respectTransparency false in
/-- A map of approximations induces the given map on the injective complex projection. -/
@[reassoc (attr := simp)]
theorem approximationMap_fst {M N : CochainComplex C ℤ} (f : M ⟶ N) :
    approximationMap f ≫ mappingCocone.fst (cokernel.π (injectiveComparison N)) =
      mappingCocone.fst (cokernel.π (injectiveComparison M)) ≫ injectiveComplexMap f := by
  dsimp only [approximationMap]
  simp only [mappingCocone.lift_fst]

/-- The injective degreewise factor is the actual first summand of the mapping cocone. -/
noncomputable def injectiveSummand (M : CochainComplex C ℤ) (n : ℤ) :
    (injectiveComplex M).X n ⟶ (approximationComplex M).X n :=
  (mappingCocone.inl (cokernel.π (injectiveComparison M))).v n n (add_zero n)

/-- Projection onto the injective summand is a genuine retraction. -/
instance injectiveSummand_mono (M : CochainComplex C ℤ) (n : ℤ) :
    Mono (injectiveSummand M n) := by
  exact mono_of_mono_fac (mappingCocone.inl_v_fst_f (cokernel.π (injectiveComparison M)) n)

set_option backward.isDefEq.respectTransparency false in
/-- The actual injective summand and the displayed original embedding supply the factor data. -/
noncomputable def injectiveFactor (M : CochainComplex C ℤ) (n : ℤ) :
    Subobject.InjectiveFactor ((approximationComparison.app M).f n) := by
  letI := injectiveSummand_mono M n
  have hI : Injective ((injectiveComplex M).X n) := by
    change Injective (HasFunctorialInjectives.obj (M.X n) ⊞
      HasFunctorialInjectives.obj (M.X (n + 1)))
    infer_instance
  exact {
    subobject := Subobject.mk (injectiveSummand M n)
    injective := Injective.of_iso (Subobject.underlyingIso (injectiveSummand M n)).symm hI
    lift := (injectiveComparison M).f n ≫ (Subobject.underlyingIso (injectiveSummand M n)).inv
    lift_arrow := by
      rw [Category.assoc, Subobject.underlyingIso_arrow]
      dsimp only [approximationComparison, injectiveSummand]
      apply mappingCocone_ext (cokernel.π (injectiveComparison M))
      · simp only [Category.assoc, mappingCocone.inl_v_fst_f, Category.comp_id,
          mappingCocone.lift_f_fst_f]
      · simp only [Category.assoc, mappingCocone.inl_v_snd_v, comp_zero,
          mappingCocone.lift_f_snd_v, HomComplex.Cochain.zero_v] }

set_option backward.isDefEq.respectTransparency false in
/-- The concrete source construction using supplied functorial injective embeddings. -/
noncomputable def ofFunctorialInjectives : WithInjectiveFactors C where
  toFunctor := approximationFunctor
  ι := approximationComparison
  mono_app M := by
    letI := injectiveComparison_mono M
    exact mono_of_mono_fac (approximationComparison_fst M)
  quasiIso_app M := by
    letI := injectiveComparison_mono M
    exact quasiIso_mappingCocone_lift (injectiveComparison M)
  factor := injectiveFactor

/-- The approximation uses the displayed mapping cocone on every input. -/
@[simp]
theorem ofFunctorialInjectives_obj (M : CochainComplex C ℤ) :
    ((ofFunctorialInjectives (C := C)).toFunctor.obj M) = approximationComplex M := rfl

/-- The selected factor is the actual injective summand. -/
@[simp]
theorem ofFunctorialInjectives_factor (M : CochainComplex C ℤ) (n : ℤ) :
    (ofFunctorialInjectives (C := C)).factor M n = injectiveFactor M n := rfl

end Construction

section Grothendieck

variable {C : Type u} [Category.{v} C] [Abelian C]

/-- Lemma 19.12.5: every Grothendieck abelian category admits a functorial monomorphic
quasi-isomorphic complex approximation whose comparison maps factor degreewise through injective
subobjects. -/
@[stacks 079N "bundled existence"]
theorem nonempty [IsGrothendieckAbelian.{w} C] :
    Nonempty (WithInjectiveFactors C) := ⟨ofFunctorialInjectives⟩

/-- The unbundled existential view of an approximation with injective degreewise factors. -/
@[stacks 079N "existential view"]
theorem exists_approximation [IsGrothendieckAbelian.{w} C] :
    ∃ J : FunctorialComplexApproximation C,
      ∀ (M : CochainComplex C ℤ) (n : ℤ),
        ∃ I : Subobject ((J.toFunctor.obj M).X n),
          Injective (I : C) ∧ I.Factors ((J.ι.app M).f n) := by
  let J := ofFunctorialInjectives (C := C)
  exact ⟨J.toApproximation, fun M n ↦
    ⟨(J.factor M n).subobject, (J.factor M n).injective,
      (Subobject.factors_iff _ _).mpr ⟨(J.factor M n).lift, (J.factor M n).lift_arrow⟩⟩⟩

end Grothendieck

end WithInjectiveFactors

end FunctorialComplexApproximation

end CochainComplex
