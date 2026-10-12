/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import Mathlib.Algebra.Category.ModuleCat.Monoidal.Closed
public import Mathlib.Algebra.Module.FinitePresentation
public import Mathlib.CategoryTheory.Limits.Shapes.Pullback.IsPullback.Kernels
public import Mathlib.Data.List.TFAE
public import Mathlib.Tactic.CrossRefAttribute
public import ReasLib.Algebra.Category.ModuleCat.FinitePresentation
public import ReasLib.Algebra.Homology.ShortComplex.UniversallyExact.Colimit
import Mathlib.LinearAlgebra.TensorProduct.Pi
import Mathlib.CategoryTheory.Filtered.Connected

/-!
# Criteria for universal exactness

@stack 058K
@stack 058L

The definitions in this leaf are reusable module-theoretic criteria for a
universally exact short complex.  Criteria local to a particular presentation
are scoped under `UniversallyExact.Criteria`; intrinsic closure and splitting
results live directly under `UniversallyExact`.
-/

@[expose] public section

open CategoryTheory Limits MonoidalCategory

universe u v

namespace CategoryTheory.ShortComplex

variable {R : Type u} [CommRing R]
variable {S : ShortComplex (ModuleCat.{u} R)}

namespace UniversallyExact

private noncomputable def finiteFreeTranspose
    {R : Type u} [CommRing R] {n m : ℕ}
    (d : (Fin m → R) →ₗ[R] (Fin n → R)) :
    (Fin n → R) →ₗ[R] (Fin m → R) :=
  Fintype.linearCombination R fun i j => d (Pi.single j 1) i

@[simp]
private lemma finiteFreeTranspose_apply
    {R : Type u} [CommRing R] {n m : ℕ}
    (d : (Fin m → R) →ₗ[R] (Fin n → R)) (x : Fin n → R) (j : Fin m) :
    finiteFreeTranspose d x j = ∑ i, x i * d (Pi.single j 1) i := by
  simp [finiteFreeTranspose, Fintype.linearCombination_apply, smul_eq_mul]

private lemma map_eq_sum_piSingle
    {R : Type u} [CommRing R] {n : ℕ}
    {M : Type v} [AddCommGroup M] [Module R M]
    (f : (Fin n → R) →ₗ[R] M) (x : Fin n → R) :
    f x = ∑ i, x i • f (Pi.single i 1) := by
  conv_lhs => rw [show x = ∑ i, x i • Pi.single i 1 by
    ext j
    simp [Pi.single_apply]]
  simp

private lemma map_eq_sum_finsuppSingle
    {R : Type u} [CommRing R] {n : ℕ}
    {M : Type v} [AddCommGroup M] [Module R M]
    (f : (Fin n →₀ R) →ₗ[R] M) (x : Fin n →₀ R) :
    f x = ∑ i, x i • f (Finsupp.single i 1) := by
  classical
  have hx : Finsupp.linearCombination R (fun i ↦ Finsupp.single i 1) x = x := by
    ext i
    simp [Finsupp.linearCombination_apply, Finsupp.sum_fintype]
  calc
    f x = f (Finsupp.linearCombination R (fun i ↦ Finsupp.single i 1) x) := by rw [hx]
    _ = Finsupp.linearCombination R (fun i ↦ f (Finsupp.single i 1)) x :=
      Finsupp.apply_linearCombination R f _ x
    _ = ∑ i, x i • f (Finsupp.single i 1) := by
      simp only [Finsupp.linearCombination_apply, Finsupp.sum_fintype, zero_smul,
        implies_true]

private lemma piScalarRight_lTensor_finiteFreeTranspose_apply
    {R : Type u} [CommRing R] {n m : ℕ}
    {M : Type v} [AddCommGroup M] [Module R M]
    (d : (Fin m → R) →ₗ[R] (Fin n → R))
    (w : TensorProduct R M (Fin n → R)) (j : Fin m) :
    TensorProduct.piScalarRight R R M (Fin m)
        ((finiteFreeTranspose d).lTensor M w) j =
      ∑ i, d (Pi.single j 1) i •
        TensorProduct.piScalarRight R R M (Fin n) w i := by
  induction w using TensorProduct.induction_on with
  | zero => simp
  | tmul x y =>
      simp only [LinearMap.lTensor_tmul, TensorProduct.piScalarRight_apply,
        TensorProduct.piScalarRightHom_tmul, finiteFreeTranspose_apply]
      rw [Finset.sum_smul]
      apply Finset.sum_congr rfl
      intro i hi
      rw [mul_smul]
      exact smul_comm _ _ _
  | add x y hx hy =>
      simp only [map_add, Pi.add_apply, hx, hy]
      rw [← Finset.sum_add_distrib]
      apply Finset.sum_congr rfl
      intro i hi
      rw [smul_add]

private lemma piScalarRight_lTensor_apply
    {R : Type u} [CommRing R] {n m : ℕ}
    {M : Type v} [AddCommGroup M] [Module R M]
    (d : (Fin m → R) →ₗ[R] (Fin n → R))
    (w : TensorProduct R M (Fin m → R)) (i : Fin n) :
    TensorProduct.piScalarRight R R M (Fin n) ((d.lTensor M) w) i =
      ∑ j, d (Pi.single j 1) i •
        TensorProduct.piScalarRight R R M (Fin m) w j := by
  induction w using TensorProduct.induction_on with
  | zero => simp
  | tmul x y =>
      simp only [LinearMap.lTensor_tmul, TensorProduct.piScalarRight_apply,
        TensorProduct.piScalarRightHom_tmul]
      rw [map_eq_sum_piSingle d y]
      simp only [Finset.sum_apply, Pi.smul_apply]
      rw [Finset.sum_smul]
      apply Finset.sum_congr rfl
      intro j hj
      rw [smul_eq_mul, mul_smul]
      exact smul_comm _ _ _
  | add x y hx hy =>
      simp only [map_add, Pi.add_apply, hx, hy]
      rw [← Finset.sum_add_distrib]
      apply Finset.sum_congr rfl
      intro i hi
      rw [smul_add]

private lemma exists_lift_finiteFreeSquare
    {R : Type u} [CommRing R]
    {X₁ X₂ : Type v} [AddCommGroup X₁] [Module R X₁]
    [AddCommGroup X₂] [Module R X₂]
    (f : X₁ →ₗ[R] X₂)
    (hf : LinearMap.UniversallyInjective.{u, v, v, max u v} f)
    {n m : ℕ}
    (d : (Fin m → R) →ₗ[R] (Fin n → R))
    (phi : (Fin m → R) →ₗ[R] X₁)
    (psi : (Fin n → R) →ₗ[R] X₂)
    (hsq : f.comp phi = psi.comp d) :
    ∃ l : (Fin n → R) →ₗ[R] X₁, l.comp d = phi := by
  classical
  let dt : (Fin n → R) →ₗ[R] (Fin m → R) := finiteFreeTranspose d
  let Q : Type u := (Fin m → R) ⧸ LinearMap.range dt
  let q : (Fin m → R) →ₗ[R] Q := (LinearMap.range dt).mkQ
  let a : TensorProduct R X₁ (Fin m → R) :=
    ∑ j, phi (Pi.single j 1) ⊗ₜ[R] Pi.single j 1
  have hq_dt (i : Fin n) : q (dt (Pi.single i 1)) = 0 := by
    apply (Submodule.Quotient.mk_eq_zero (LinearMap.range dt)).2
    exact ⟨Pi.single i 1, rfl⟩
  have h_image : (f.rTensor Q) (q.lTensor X₁ a) = 0 := by
    simp only [a, map_sum, LinearMap.lTensor_tmul, LinearMap.rTensor_tmul]
    calc
      ∑ j, f (phi (Pi.single j 1)) ⊗ₜ[R] q (Pi.single j 1) =
          ∑ j, psi (d (Pi.single j 1)) ⊗ₜ[R] q (Pi.single j 1) := by
            apply Finset.sum_congr rfl
            intro j hj
            have hj' := LinearMap.congr_fun hsq (Pi.single j 1)
            change f (phi (Pi.single j 1)) = psi (d (Pi.single j 1)) at hj'
            rw [hj']
      _ = ∑ j, (∑ i, d (Pi.single j 1) i • psi (Pi.single i 1)) ⊗ₜ[R]
          q (Pi.single j 1) := by
            apply Finset.sum_congr rfl
            intro j hj
            rw [map_eq_sum_piSingle psi]
      _ = ∑ j, ∑ i, psi (Pi.single i 1) ⊗ₜ[R]
          q (d (Pi.single j 1) i • Pi.single j 1) := by
            apply Finset.sum_congr rfl
            intro j hj
            rw [TensorProduct.sum_tmul]
            apply Finset.sum_congr rfl
            intro i hi
            rw [TensorProduct.smul_tmul, ← map_smul]
      _ = ∑ i, psi (Pi.single i 1) ⊗ₜ[R]
          q (∑ j, d (Pi.single j 1) i • Pi.single j 1) := by
            rw [Finset.sum_comm]
            apply Finset.sum_congr rfl
            intro i hi
            rw [map_sum, TensorProduct.tmul_sum]
      _ = ∑ i, psi (Pi.single i 1) ⊗ₜ[R] q (dt (Pi.single i 1)) := by
            apply Finset.sum_congr rfl
            intro i hi
            congr 2
            ext j
            simp [dt, finiteFreeTranspose_apply, Pi.single_apply]
      _ = 0 := by simp [hq_dt]
  have hqa : q.lTensor X₁ a = 0 := by
    apply hf.rTensor_injective Q
    simpa using h_image
  have hexact : Function.Exact dt q := by
    rw [LinearMap.exact_iff, Submodule.ker_mkQ]
  have htensorExact : Function.Exact (dt.lTensor X₁) (q.lTensor X₁) :=
    lTensor_exact X₁ hexact (Submodule.mkQ_surjective _)
  obtain ⟨w, hw⟩ :
      ∃ w : TensorProduct R X₁ (Fin n → R), dt.lTensor X₁ w = a := by
    have ha : a ∈ LinearMap.ker (q.lTensor X₁) := by
      simpa [LinearMap.mem_ker] using hqa
    rw [htensorExact.linearMap_ker_eq] at ha
    exact ha
  let z : Fin n → X₁ := TensorProduct.piScalarRight R R X₁ (Fin n) w
  let l : (Fin n → R) →ₗ[R] X₁ := Fintype.linearCombination R z
  have hl_basis (j : Fin m) : l (d (Pi.single j 1)) = phi (Pi.single j 1) := by
    have hwj := congr_fun
      (congr_arg (TensorProduct.piScalarRight R R X₁ (Fin m)) hw) j
    rw [piScalarRight_lTensor_finiteFreeTranspose_apply d w j] at hwj
    simp only [a, map_sum, TensorProduct.piScalarRight_apply,
      TensorProduct.piScalarRightHom_tmul, Finset.sum_apply, Pi.single_apply,
      ite_smul, one_smul, zero_smul] at hwj
    rw [Fintype.linearCombination_apply]
    simpa [l, z] using hwj
  refine ⟨l, LinearMap.ext fun x => ?_⟩
  change l (d x) = phi x
  rw [map_eq_sum_piSingle d x, map_sum, map_eq_sum_piSingle phi x]
  apply Finset.sum_congr rfl
  intro j hj
  rw [map_smul, hl_basis]

/-- Tensoring a universally exact short complex on the right by any module is short exact. -/
theorem tensorRight_shortExact
    (hU : S.UniversallyExact) (Q : ModuleCat.{u} R) :
    (S.map (MonoidalCategory.tensorRight Q)).ShortExact := by
  have hExact : Function.Exact S.f.hom S.g.hom :=
    (ShortComplex.ShortExact.moduleCat_exact_iff_function_exact S).mp hU.shortExact.exact
  apply ModuleCat.shortComplex_shortExact
  · change Function.Exact (S.f.hom.rTensor Q) (S.g.hom.rTensor Q)
    exact rTensor_exact Q hExact hU.shortExact.moduleCat_surjective_g
  · change Function.Injective (S.f.hom.rTensor Q)
    exact hU.universallyInjective_f.rTensor_injective Q
  · change Function.Surjective (S.g.hom.rTensor Q)
    exact LinearMap.rTensor_surjective Q hU.shortExact.moduleCat_surjective_g

/-- Universal exactness is invariant under isomorphism of short complexes. -/
theorem of_iso {T : ShortComplex (ModuleCat.{u} R)} (e : T ≅ S)
    (hT : T.UniversallyExact) : S.UniversallyExact := by
  refine ⟨ShortComplex.shortExact_of_iso e hT.shortExact, ?_⟩
  intro Q _ _
  let Qc : ModuleCat.{u} R := ModuleCat.of R Q
  have hTQ : (T.map (MonoidalCategory.tensorRight Qc)).ShortExact :=
    tensorRight_shortExact hT Qc
  have hSQ : (S.map (MonoidalCategory.tensorRight Qc)).ShortExact :=
    ShortComplex.shortExact_of_iso
      ((MonoidalCategory.tensorRight Qc).mapShortComplex.mapIso e) hTQ
  change Function.Injective
    ((S.map (MonoidalCategory.tensorRight Qc)).f.hom)
  exact hSQ.moduleCat_injective_f

namespace Criteria

/-- Exactness after right tensoring with every finitely presented module. -/
@[stacks 058K "tensor criterion for universal exactness"]
def tensorRight (S : ShortComplex (ModuleCat.{u} R)) : Prop :=
  ∀ (Q : ModuleCat.{u} R) [Module.FinitePresentation R Q],
    (S.map (MonoidalCategory.tensorRight Q)).ShortExact

/-- The finite equational lifting criterion for the first map of a short complex. -/
@[stacks 058K "equational criterion for universal exactness"]
def equational (S : ShortComplex (ModuleCat.{u} R)) : Prop :=
  ∀ {n m : ℕ} (x : Fin n → S.X₁) (y : Fin m → S.X₂) (a : Fin n → Fin m → R),
    (∀ i, S.f.hom (x i) = ∑ j, a i j • y j) →
      ∃ z : Fin m → S.X₁, ∀ i, x i = ∑ j, a i j • z j

/-- The finite-free square lifting criterion for the first map of a short complex. -/
@[stacks 058K "finite-free lifting criterion for universal exactness"]
def finiteFreeSquare (S : ShortComplex (ModuleCat.{u} R)) : Prop :=
  ∀ {n m : ℕ}
    (u : ModuleCat.of R (Fin n →₀ R) ⟶ ModuleCat.of R (Fin m →₀ R))
    (phi : ModuleCat.of R (Fin n →₀ R) ⟶ S.X₁)
    (psi : ModuleCat.of R (Fin m →₀ R) ⟶ S.X₂),
    CommSq u phi psi S.f → ∃ l : ModuleCat.of R (Fin m →₀ R) ⟶ S.X₁, u ≫ l = phi

/-- Postcomposition with the second map is surjective on maps from finitely presented modules. -/
@[stacks 058K "Hom-surjectivity criterion for universal exactness"]
def homSurjective (S : ShortComplex (ModuleCat.{u} R)) : Prop :=
  ∀ (P : ModuleCat.{u} R) [Module.FinitePresentation R P],
    Function.Surjective fun phi : P ⟶ S.X₂ ↦ phi ≫ S.g

/-- A filtered split-colimit presentation with constant left term and finitely presented
cokernels. -/
@[stacks 058K "filtered split-colimit criterion for universal exactness"]
def filteredSplitColimit (S : ShortComplex (ModuleCat.{u} R)) : Prop :=
  ∃ (J : Type u) (_ : Category.{u} J) (_ : IsFiltered J)
    (F : J ⥤ ShortComplex (ModuleCat.{u} R))
    (_ : F ⋙ ShortComplex.π₁ ≅ (Functor.const J).obj S.X₁)
    (_ : ∀ j, Nonempty ((F.obj j).Splitting))
    (_ : ∀ j, Module.FinitePresentation R (F.obj j).X₃),
    ∃ e : colimit F ⟶ S, IsIso e

private abbrev presentationMap
    {J : Type u} [Category.{u} J]
    {X : ModuleCat.{u} R} (P : ColimitPresentation J X) (j : J) :
    P.diag.obj j ⟶ X := P.ι.app j

@[reassoc]
private lemma presentationMap_naturality
    {J : Type u} [Category.{u} J]
    {X : ModuleCat.{u} R} (P : ColimitPresentation J X)
    {i j : J} (a : i ⟶ j) :
    P.diag.map a ≫ presentationMap P j = presentationMap P i :=
  P.w a

private noncomputable abbrev pullbackStage
    {J : Type u} [Category.{u} J]
    (S : ShortComplex (ModuleCat.{u} R))
    (P : ColimitPresentation J S.X₃) (j : J) :
    ShortComplex (ModuleCat.{u} R) where
  X₁ := S.X₁
  X₂ := pullback S.g (presentationMap P j)
  X₃ := P.diag.obj j
  f := pullback.lift S.f 0 (by simp)
  g := pullback.snd S.g (presentationMap P j)
  zero := pullback.lift_snd _ _ _

@[simp, reassoc]
private lemma pullbackStage_f_fst
    {J : Type u} [Category.{u} J]
    (S : ShortComplex (ModuleCat.{u} R))
    (P : ColimitPresentation J S.X₃) (j : J) :
    (pullbackStage S P j).f ≫ pullback.fst S.g (presentationMap P j) = S.f :=
  pullback.lift_fst _ _ _

@[simp, reassoc]
private lemma pullbackStage_f_snd
    {J : Type u} [Category.{u} J]
    (S : ShortComplex (ModuleCat.{u} R))
    (P : ColimitPresentation J S.X₃) (j : J) :
    (pullbackStage S P j).f ≫ pullback.snd S.g (presentationMap P j) = 0 :=
  pullback.lift_snd _ _ _

private noncomputable abbrev pullbackStageMap
    {J : Type u} [Category.{u} J]
    (S : ShortComplex (ModuleCat.{u} R))
    (P : ColimitPresentation J S.X₃) {i j : J} (a : i ⟶ j) :
    pullbackStage S P i ⟶ pullbackStage S P j where
  τ₁ := 𝟙 _
  τ₂ := pullback.lift
    (pullback.fst S.g (presentationMap P i))
    (pullback.snd S.g (presentationMap P i) ≫ P.diag.map a) (by
      simpa only [Category.assoc, presentationMap_naturality] using
        pullback.condition)
  τ₃ := P.diag.map a
  comm₁₂ := by
    apply pullback.hom_ext
    · calc
        (𝟙 _ ≫ (pullbackStage S P j).f) ≫
            pullback.fst S.g (presentationMap P j) = S.f := by
              simpa only [Category.id_comp] using pullbackStage_f_fst S P j
        _ = ((pullbackStage S P i).f ≫
            pullback.lift (pullback.fst S.g (presentationMap P i))
              (pullback.snd S.g (presentationMap P i) ≫ P.diag.map a) _) ≫
              pullback.fst S.g (presentationMap P j) := by
                rw [Category.assoc, pullback.lift_fst]
                exact (pullbackStage_f_fst S P i).symm
    · calc
        (𝟙 _ ≫ (pullbackStage S P j).f) ≫
            pullback.snd S.g (presentationMap P j) = 0 := by
              simpa only [Category.id_comp] using pullbackStage_f_snd S P j
        _ = ((pullbackStage S P i).f ≫
            pullback.lift (pullback.fst S.g (presentationMap P i))
              (pullback.snd S.g (presentationMap P i) ≫ P.diag.map a) _) ≫
              pullback.snd S.g (presentationMap P j) := by
                symm
                rw [Category.assoc, pullback.lift_snd, ← Category.assoc,
                  pullbackStage_f_snd, zero_comp]
  comm₂₃ := pullback.lift_snd _ _ _

@[simp, reassoc]
private lemma pullbackStageMap_fst
    {J : Type u} [Category.{u} J]
    (S : ShortComplex (ModuleCat.{u} R))
    (P : ColimitPresentation J S.X₃) {i j : J} (a : i ⟶ j) :
    (pullbackStageMap S P a).τ₂ ≫ pullback.fst S.g (presentationMap P j) =
      pullback.fst S.g (presentationMap P i) :=
  pullback.lift_fst _ _ _

@[simp, reassoc]
private lemma pullbackStageMap_snd
    {J : Type u} [Category.{u} J]
    (S : ShortComplex (ModuleCat.{u} R))
    (P : ColimitPresentation J S.X₃) {i j : J} (a : i ⟶ j) :
    (pullbackStageMap S P a).τ₂ ≫ pullback.snd S.g (presentationMap P j) =
      pullback.snd S.g (presentationMap P i) ≫ P.diag.map a :=
  pullback.lift_snd _ _ _

@[simp]
private lemma pullbackStageMap_τ₁
    {J : Type u} [Category.{u} J]
    (S : ShortComplex (ModuleCat.{u} R))
    (P : ColimitPresentation J S.X₃) {i j : J} (a : i ⟶ j) :
    (pullbackStageMap S P a).τ₁ = 𝟙 S.X₁ := rfl

@[simp]
private lemma pullbackStageMap_τ₃
    {J : Type u} [Category.{u} J]
    (S : ShortComplex (ModuleCat.{u} R))
    (P : ColimitPresentation J S.X₃) {i j : J} (a : i ⟶ j) :
    (pullbackStageMap S P a).τ₃ = P.diag.map a := rfl

private noncomputable abbrev pullbackDiagram
    {J : Type u} [Category.{u} J]
    (S : ShortComplex (ModuleCat.{u} R))
    (P : ColimitPresentation J S.X₃) :
    J ⥤ ShortComplex (ModuleCat.{u} R) where
  obj := pullbackStage S P
  map := pullbackStageMap S P
  map_id j := by
    apply ShortComplex.Hom.ext
    · simp only [id_τ₁]
    · apply pullback.hom_ext
      · rw [pullbackStageMap_fst, id_τ₂, Category.id_comp]
      · rw [pullbackStageMap_snd, Functor.map_id, Category.comp_id,
          id_τ₂, Category.id_comp]
    · simp only [Functor.map_id, id_τ₃]
  map_comp a b := by
    apply ShortComplex.Hom.ext
    · simp only [comp_τ₁, Category.id_comp]
    · apply pullback.hom_ext
      · rw [pullbackStageMap_fst, comp_τ₂, Category.assoc,
          pullbackStageMap_fst, pullbackStageMap_fst]
      · rw [pullback.lift_snd, Functor.map_comp, comp_τ₂,
          Category.assoc, pullback.lift_snd]
        exact (pullbackStageMap_snd_assoc S P a (P.diag.map b)).symm
    · simp only [Functor.map_comp, comp_τ₃]

private noncomputable def pullbackDiagramLeftIso
    {J : Type u} [Category.{u} J]
    (S : ShortComplex (ModuleCat.{u} R))
    (P : ColimitPresentation J S.X₃) :
    pullbackDiagram S P ⋙ ShortComplex.π₁ ≅ (Functor.const J).obj S.X₁ :=
  NatIso.ofComponents (fun _ ↦ Iso.refl _) (by
    intro i j a
    change (𝟙 S.X₁) ≫ 𝟙 S.X₁ = 𝟙 S.X₁ ≫ 𝟙 S.X₁
    simp)

private noncomputable def pullbackDiagramRightIso
    {J : Type u} [Category.{u} J]
    (S : ShortComplex (ModuleCat.{u} R))
    (P : ColimitPresentation J S.X₃) :
    pullbackDiagram S P ⋙ ShortComplex.π₃ ≅ P.diag :=
  NatIso.ofComponents (fun _ ↦ Iso.refl _) (by
    intro i j a
    change P.diag.map a ≫ 𝟙 _ = 𝟙 _ ≫ P.diag.map a
    simp)

private noncomputable abbrev pullbackStageToOriginal
    {J : Type u} [Category.{u} J]
    (S : ShortComplex (ModuleCat.{u} R))
    (P : ColimitPresentation J S.X₃) (j : J) :
    pullbackStage S P j ⟶ S where
  τ₁ := 𝟙 _
  τ₂ := pullback.fst S.g (presentationMap P j)
  τ₃ := presentationMap P j
  comm₁₂ := (pullbackStage_f_fst S P j).symm
  comm₂₃ := pullback.condition

private noncomputable def pullbackCocone
    {J : Type u} [Category.{u} J]
    (S : ShortComplex (ModuleCat.{u} R))
    (P : ColimitPresentation J S.X₃) :
    Cocone (pullbackDiagram S P) :=
  Cocone.mk S
    { app := pullbackStageToOriginal S P
      naturality := by
        intro i j a
        apply ShortComplex.Hom.ext
        · change (𝟙 S.X₁) ≫ 𝟙 S.X₁ = 𝟙 S.X₁ ≫ 𝟙 S.X₁
          simp
        · change (pullbackStageMap S P a).τ₂ ≫
            pullback.fst S.g (presentationMap P j) =
              pullback.fst S.g (presentationMap P i) ≫ 𝟙 S.X₂
          rw [pullbackStageMap_fst, Category.comp_id]
        · change P.diag.map a ≫ presentationMap P j =
            presentationMap P i ≫ 𝟙 S.X₃
          rw [presentationMap_naturality, Category.comp_id] }

private noncomputable def pullbackCoconeLeftIsColimit
    {J : Type u} [Category.{u} J] [IsConnected J]
    (S : ShortComplex (ModuleCat.{u} R))
    (P : ColimitPresentation J S.X₃) :
    IsColimit (ShortComplex.π₁.mapCocone (pullbackCocone S P)) := by
  change IsColimit (constCocone J S.X₁)
  exact isColimitConstCocone J S.X₁

private noncomputable def pullbackCoconeRightIsColimit
    {J : Type u} [Category.{u} J]
    (S : ShortComplex (ModuleCat.{u} R))
    (P : ColimitPresentation J S.X₃) :
    IsColimit (ShortComplex.π₃.mapCocone (pullbackCocone S P)) := by
  change IsColimit P.cocone
  exact P.isColimit

private theorem pullbackStage_shortExact
    {J : Type u} [Category.{u} J]
    (S : ShortComplex (ModuleCat.{u} R)) (hS : S.ShortExact)
    (P : ColimitPresentation J S.X₃) (j : J) :
    (pullbackStage S P j).ShortExact := by
  letI : Mono S.f := hS.mono_f
  letI : Epi S.g := hS.epi_g
  haveI : Mono (pullbackStage S P j).f :=
    mono_of_mono_fac (pullbackStage_f_fst S P j)
  haveI : Epi (pullbackStage S P j).g := by
    dsimp only [pullbackStage]
    infer_instance
  have hker : IsLimit (KernelFork.ofι
      (pullbackStage S P j).f (pullbackStage S P j).zero) := by
    apply KernelFork.IsLimit.ofι'
    intro A k hk
    let l : A ⟶ S.X₁ := hS.exact.lift
      (k ≫ pullback.fst S.g (presentationMap P j)) (by
        rw [Category.assoc, pullback.condition, ← Category.assoc]
        change k ≫ (pullbackStage S P j).g ≫ presentationMap P j = 0
        rw [← Category.assoc, hk, zero_comp])
    refine ⟨l, ?_⟩
    apply pullback.hom_ext
    · rw [Category.assoc, pullbackStage_f_fst]
      exact hS.exact.lift_f _ _
    · rw [Category.assoc, pullbackStage_f_snd, comp_zero]
      exact hk.symm
  exact ShortExact.mk'
    ((pullbackStage S P j).exact_of_f_is_kernel hker) inferInstance inferInstance

private theorem pullbackStage_splitting
    {J : Type u} [Category.{u} J]
    (S : ShortComplex (ModuleCat.{u} R)) (hS : S.ShortExact)
    (P : ColimitPresentation J S.X₃) (hHom : homSurjective S) (j : J)
    [Module.FinitePresentation R (P.diag.obj j)] :
    Nonempty ((pullbackStage S P j).Splitting) := by
  obtain ⟨t, ht⟩ := hHom (P.diag.obj j) (presentationMap P j)
  let s : P.diag.obj j ⟶ pullback S.g (presentationMap P j) :=
    pullback.lift t (𝟙 _) (by simpa only [Category.id_comp] using ht)
  have hs : s ≫ (pullbackStage S P j).g = 𝟙 _ := by
    exact pullback.lift_snd _ _ _
  let hStage := pullbackStage_shortExact S hS P j
  exact ⟨ShortComplex.Splitting.ofExactOfSection _ hStage.exact s hs hStage.mono_f⟩

private lemma exists_lift_pi_of_finiteFreeSquare
    (hSquare : finiteFreeSquare S) {n m : ℕ}
    (d : (Fin m → R) →ₗ[R] (Fin n → R))
    (phi : (Fin m → R) →ₗ[R] S.X₁)
    (psi : (Fin n → R) →ₗ[R] S.X₂)
    (hsq : S.f.hom.comp phi = psi.comp d) :
    ∃ l : (Fin n → R) →ₗ[R] S.X₁, l.comp d = phi := by
  classical
  let em : (Fin m →₀ R) ≃ₗ[R] (Fin m → R) :=
    Finsupp.linearEquivFunOnFinite R R (Fin m)
  let en : (Fin n →₀ R) ≃ₗ[R] (Fin n → R) :=
    Finsupp.linearEquivFunOnFinite R R (Fin n)
  let uLin : (Fin m →₀ R) →ₗ[R] (Fin n →₀ R) :=
    en.symm.toLinearMap.comp (d.comp em.toLinearMap)
  let phiLin : (Fin m →₀ R) →ₗ[R] S.X₁ := phi.comp em.toLinearMap
  let psiLin : (Fin n →₀ R) →ₗ[R] S.X₂ := psi.comp en.toLinearMap
  let u : ModuleCat.of R (Fin m →₀ R) ⟶ ModuleCat.of R (Fin n →₀ R) :=
    ModuleCat.ofHom uLin
  let phi' : ModuleCat.of R (Fin m →₀ R) ⟶ S.X₁ := ModuleCat.ofHom phiLin
  let psi' : ModuleCat.of R (Fin n →₀ R) ⟶ S.X₂ := ModuleCat.ofHom psiLin
  have hcomm : CommSq u phi' psi' S.f := by
    constructor
    apply ModuleCat.hom_ext
    apply LinearMap.ext
    intro w
    change psi (en (en.symm (d (em w)))) = S.f.hom (phi (em w))
    simpa using (LinearMap.congr_fun hsq (em w)).symm
  obtain ⟨l', hl'⟩ := hSquare u phi' psi' hcomm
  let l : (Fin n → R) →ₗ[R] S.X₁ := l'.hom.comp en.symm.toLinearMap
  refine ⟨l, LinearMap.ext fun w ↦ ?_⟩
  have hw := ConcreteCategory.congr_hom hl' (em.symm w)
  change l'.hom (uLin (em.symm w)) = phiLin (em.symm w) at hw
  simpa [l, uLin, phiLin, em, en] using hw

/-- Exactness after tensoring with finitely presented modules implies the finite equational
lifting criterion. -/
@[stacks 058K "(2) implies (3)"]
theorem equational_of_tensorRight (hTensor : tensorRight S) : equational S := by
  classical
  intro n m x y a hxy
  let d : (Fin m → R) →ₗ[R] (Fin n → R) :=
    Fintype.linearCombination R fun j i ↦ a i j
  have hd_basis (j : Fin m) (i : Fin n) : d (Pi.single j 1) i = a i j := by
    rw [Fintype.linearCombination_apply]
    simp only [Pi.single_apply, ite_smul, one_smul, zero_smul]
    rw [Finset.sum_eq_single j]
    · simp
    · intro b hb hbj
      simp [hbj]
    · simp
  let Q : Type u := (Fin n → R) ⧸ LinearMap.range d
  let q : (Fin n → R) →ₗ[R] Q := (LinearMap.range d).mkQ
  letI : Module.FinitePresentation R Q :=
    Module.finitePresentation_of_surjective q (Submodule.mkQ_surjective _)
      (by
        rw [show LinearMap.ker q = LinearMap.range d by simp [q, Q]]
        exact Submodule.fg_range d)
  let v : TensorProduct R S.X₁ (Fin n → R) :=
    ∑ i, x i ⊗ₜ[R] Pi.single i 1
  have hq_d (j : Fin m) : q (d (Pi.single j 1)) = 0 := by
    apply (Submodule.Quotient.mk_eq_zero (LinearMap.range d)).2
    exact ⟨Pi.single j 1, rfl⟩
  have h_image : (S.f.hom.rTensor Q) (q.lTensor S.X₁ v) = 0 := by
    simp only [v, map_sum, LinearMap.lTensor_tmul, LinearMap.rTensor_tmul]
    calc
      ∑ i, S.f.hom (x i) ⊗ₜ[R] q (Pi.single i 1) =
          ∑ i, (∑ j, a i j • y j) ⊗ₜ[R] q (Pi.single i 1) := by
            apply Finset.sum_congr rfl
            intro i hi
            rw [hxy i]
      _ = ∑ i, ∑ j, y j ⊗ₜ[R] q (a i j • Pi.single i 1) := by
            apply Finset.sum_congr rfl
            intro i hi
            rw [TensorProduct.sum_tmul]
            apply Finset.sum_congr rfl
            intro j hj
            rw [TensorProduct.smul_tmul, ← map_smul]
      _ = ∑ j, y j ⊗ₜ[R] q (∑ i, a i j • Pi.single i 1) := by
            rw [Finset.sum_comm]
            apply Finset.sum_congr rfl
            intro j hj
            rw [map_sum, TensorProduct.tmul_sum]
      _ = ∑ j, y j ⊗ₜ[R] q (d (Pi.single j 1)) := by
            apply Finset.sum_congr rfl
            intro j hj
            congr 2
            ext i
            simp [hd_basis, Pi.single_apply]
      _ = 0 := by simp [hq_d]
  have hqv : q.lTensor S.X₁ v = 0 := by
    have hinj := (hTensor (ModuleCat.of R Q)).moduleCat_injective_f
    change Function.Injective (S.f.hom.rTensor Q) at hinj
    apply hinj
    simpa using h_image
  have hexact : Function.Exact d q := by
    rw [LinearMap.exact_iff, Submodule.ker_mkQ]
  have htensorExact : Function.Exact (d.lTensor S.X₁) (q.lTensor S.X₁) :=
    lTensor_exact S.X₁ hexact (Submodule.mkQ_surjective _)
  obtain ⟨w, hw⟩ : ∃ w : TensorProduct R S.X₁ (Fin m → R), d.lTensor S.X₁ w = v := by
    have hv : v ∈ LinearMap.ker (q.lTensor S.X₁) := by
      simpa [LinearMap.mem_ker] using hqv
    rw [htensorExact.linearMap_ker_eq] at hv
    exact hv
  let z : Fin m → S.X₁ := TensorProduct.piScalarRight R R S.X₁ (Fin m) w
  refine ⟨z, fun i ↦ ?_⟩
  have hwi := congr_fun
    (congr_arg (TensorProduct.piScalarRight R R S.X₁ (Fin n)) hw) i
  rw [piScalarRight_lTensor_apply d w i] at hwi
  simp_rw [hd_basis] at hwi
  simp only [v, map_sum, TensorProduct.piScalarRight_apply,
    TensorProduct.piScalarRightHom_tmul, Finset.sum_apply, Pi.single_apply,
    ite_smul, one_smul, zero_smul] at hwi
  simpa [z] using hwi.symm

/-- The finite equational lifting criterion implies the finite-free square lifting
criterion. -/
@[stacks 058K "(3) implies (4)"]
theorem finiteFreeSquare_of_equational (hEq : equational S) : finiteFreeSquare S := by
  classical
  intro n m u phi psi hsq
  let x : Fin n → S.X₁ := fun i ↦ phi.hom (Finsupp.single i 1)
  let y : Fin m → S.X₂ := fun j ↦ psi.hom (Finsupp.single j 1)
  let a : Fin n → Fin m → R := fun i j ↦ u.hom (Finsupp.single i 1) j
  have hxy (i : Fin n) : S.f.hom (x i) = ∑ j, a i j • y j := by
    have hcomm := ConcreteCategory.congr_hom hsq.w (Finsupp.single i 1)
    change psi.hom (u.hom (Finsupp.single i 1)) =
      S.f.hom (phi.hom (Finsupp.single i 1)) at hcomm
    calc
      S.f.hom (x i) = psi.hom (u.hom (Finsupp.single i 1)) := hcomm.symm
      _ = ∑ j, u.hom (Finsupp.single i 1) j •
          psi.hom (Finsupp.single j 1) :=
        map_eq_sum_finsuppSingle psi.hom _
      _ = ∑ j, a i j • y j := rfl
  obtain ⟨z, hz⟩ := hEq x y a hxy
  let l : (Fin m →₀ R) →ₗ[R] S.X₁ := Finsupp.linearCombination R z
  refine ⟨ModuleCat.ofHom l, ?_⟩
  apply ModuleCat.hom_ext
  apply Finsupp.basisSingleOne.ext
  intro i
  change l (u.hom (Finsupp.single i 1)) = phi.hom (Finsupp.single i 1)
  rw [map_eq_sum_finsuppSingle l]
  simpa [l, x, a, Finsupp.linearCombination_apply, Finsupp.sum_fintype,
    Finsupp.single_apply] using (hz i).symm

/-- The finite-free square lifting criterion implies surjectivity on maps from every finitely
presented module. -/
@[stacks 058K "(4) implies (5)"]
theorem homSurjective_of_finiteFreeSquare (hS : S.ShortExact)
    (hSquare : finiteFreeSquare S) : homSurjective S := by
  classical
  intro P _ tau
  obtain ⟨n, K, e, hK⟩ := Module.FinitePresentation.exists_fin R P
  obtain ⟨m, k, hk⟩ := Submodule.fg_iff_exists_fin_generating_family.mp hK
  let d : (Fin m → R) →ₗ[R] (Fin n → R) := Fintype.linearCombination R k
  have hd : LinearMap.range d = K := by
    simpa [d] using (Fintype.range_linearCombination R k).trans hk
  let q : (Fin n → R) →ₗ[R] P := e.symm.toLinearMap.comp K.mkQ
  choose y hy using fun i : Fin n ↦
    hS.moduleCat_surjective_g (tau.hom (q (Pi.single i 1)))
  let psi : (Fin n → R) →ₗ[R] S.X₂ := Fintype.linearCombination R y
  have hgpsi : S.g.hom.comp psi = tau.hom.comp q := by
    apply LinearMap.ext
    intro w
    change S.g.hom (psi w) = tau.hom (q w)
    rw [map_eq_sum_piSingle psi w, map_eq_sum_piSingle q w, map_sum, map_sum]
    apply Finset.sum_congr rfl
    intro i hi
    rw [map_smul, map_smul]
    simp [psi, Fintype.linearCombination_apply, Pi.single_apply, hy]
  have hqd : q.comp d = 0 := by
    apply LinearMap.ext
    intro w
    change e.symm (K.mkQ (d w)) = 0
    have hdw : d w ∈ K := by
      rw [← hd]
      exact LinearMap.mem_range_self d w
    change e.symm (Submodule.Quotient.mk (d w)) = 0
    rw [(Submodule.Quotient.mk_eq_zero K).2 hdw]
    simp
  have hcycle (j : Fin m) : S.g.hom (psi (d (Pi.single j 1))) = 0 := by
    calc
      S.g.hom (psi (d (Pi.single j 1))) = tau.hom (q (d (Pi.single j 1))) :=
        LinearMap.congr_fun hgpsi (d (Pi.single j 1))
      _ = 0 := by
        have hj := LinearMap.congr_fun hqd (Pi.single j 1)
        change q (d (Pi.single j 1)) = 0 at hj
        rw [hj, map_zero]
  choose x hx using fun j ↦ (S.moduleCat_exact_iff.mp hS.exact)
    (psi (d (Pi.single j 1))) (hcycle j)
  let phi : (Fin m → R) →ₗ[R] S.X₁ := Fintype.linearCombination R x
  have hphi_basis (j : Fin m) : phi (Pi.single j 1) = x j := by
    simp [phi, Fintype.linearCombination_apply, Pi.single_apply]
  have hfphi : S.f.hom.comp phi = psi.comp d := by
    apply LinearMap.ext
    intro w
    change S.f.hom (phi w) = psi (d w)
    rw [map_eq_sum_piSingle phi w, map_eq_sum_piSingle d w, map_sum, map_sum]
    apply Finset.sum_congr rfl
    intro j hj
    rw [map_smul, map_smul, hphi_basis, hx]
  obtain ⟨l, hl⟩ := exists_lift_pi_of_finiteFreeSquare hSquare d phi psi hfphi
  let psi' : (Fin n → R) →ₗ[R] S.X₂ := psi - S.f.hom.comp l
  have hpsi'd : psi'.comp d = 0 := by
    apply LinearMap.ext
    intro w
    change psi (d w) - S.f.hom (l (d w)) = 0
    have hlw := LinearMap.congr_fun hl w
    change l (d w) = phi w at hlw
    have hfw := LinearMap.congr_fun hfphi w
    change S.f.hom (phi w) = psi (d w) at hfw
    rw [hlw, hfw, sub_self]
  have hgpsi' : S.g.hom.comp psi' = tau.hom.comp q := by
    apply LinearMap.ext
    intro w
    change S.g.hom (psi w - S.f.hom (l w)) = tau.hom (q w)
    rw [map_sub, S.moduleCat_zero_apply, sub_zero]
    exact LinearMap.congr_fun hgpsi w
  have hKker : K ≤ LinearMap.ker psi' := by
    rw [← hd]
    exact LinearMap.range_le_ker_iff.mpr hpsi'd
  let liftLin : P →ₗ[R] S.X₂ := (K.liftQ psi' hKker).comp e.toLinearMap
  refine ⟨ModuleCat.ofHom liftLin, ?_⟩
  apply ModuleCat.hom_ext
  apply LinearMap.ext
  intro z
  obtain ⟨z', hz'⟩ := Submodule.mkQ_surjective K (e z)
  change S.g.hom (K.liftQ psi' hKker (e z)) = tau.hom z
  rw [← hz']
  change S.g.hom (psi' z') = tau.hom z
  have hg := LinearMap.congr_fun hgpsi' z'
  change S.g.hom (psi' z') = tau.hom (q z') at hg
  rw [hg]
  change tau.hom (e.symm (K.mkQ z')) = tau.hom z
  rw [hz', e.symm_apply_apply]

/-- Surjectivity on maps from finitely presented modules gives a filtered presentation by
split short exact complexes. -/
@[stacks 058K "(5) implies (6)"]
theorem filteredSplitColimit_of_homSurjective (hS : S.ShortExact)
    (hHom : homSurjective S) : filteredSplitColimit S := by
  classical
  obtain ⟨J, hJ, hFiltered, P, hP⟩ :=
    ModuleCat.isFinitePresentation_ind (R := R) S.X₃
  letI : SmallCategory J := hJ
  letI : IsFiltered J := hFiltered
  letI : IsConnected J := IsFiltered.isConnected J
  let F : J ⥤ ShortComplex (ModuleCat.{u} R) := pullbackDiagram S P
  refine ⟨J, inferInstance, inferInstance, F, ?_, ?_, ?_, ?_⟩
  · simpa only [F] using pullbackDiagramLeftIso S P
  · intro j
    letI : Module.FinitePresentation R (P.diag.obj j) := hP j
    simpa only [F] using pullbackStage_splitting S hS P hHom j
  · intro j
    simpa only [F] using hP j
  · let c : Cocone F := pullbackCocone S P
    let h₁ : IsColimit (ShortComplex.π₁.mapCocone (colimit.cocone F)) :=
      isColimitOfPreserves ShortComplex.π₁ (colimit.isColimit F)
    let h₂ : IsColimit (ShortComplex.π₂.mapCocone (colimit.cocone F)) :=
      isColimitOfPreserves ShortComplex.π₂ (colimit.isColimit F)
    let h₃ : IsColimit (ShortComplex.π₃.mapCocone (colimit.cocone F)) :=
      isColimitOfPreserves ShortComplex.π₃ (colimit.isColimit F)
    let hc : IsColimit (colimit.cocone F) :=
      ShortComplex.isColimitOfIsColimitπ _ h₁ h₂ h₃
    let e : colimit F ⟶ S := hc.desc c
    have hF (j : J) : (F.obj j).ShortExact := by
      simpa only [F] using pullbackStage_shortExact S hS P j
    have hcolim : (colimit F).ShortExact :=
      ShortExact.colimit_of_isFiltered F hF
    let ht₁ : IsColimit (ShortComplex.π₁.mapCocone c) :=
      pullbackCoconeLeftIsColimit S P
    let ht₃ : IsColimit (ShortComplex.π₃.mapCocone c) :=
      pullbackCoconeRightIsColimit S P
    let i₁ := h₁.coconePointUniqueUpToIso ht₁
    let i₃ := h₃.coconePointUniqueUpToIso ht₃
    haveI : IsIso e.τ₁ := by
      change IsIso i₁.hom
      infer_instance
    haveI : IsIso e.τ₃ := by
      change IsIso i₃.hom
      infer_instance
    haveI : IsIso e.τ₂ :=
      ShortComplex.isIso₂_of_shortExact_of_isIso₁₃ e hcolim hS
    haveI : IsIso e := ShortComplex.isIso_of_isIso e
    exact ⟨e, inferInstance⟩

/-- A short complex presented as a filtered colimit of split short exact complexes is
universally exact. -/
@[stacks 058K "(6) implies (1)"]
theorem universallyExact_of_filteredSplitColimit
    (h : filteredSplitColimit S) : S.UniversallyExact := by
  obtain ⟨J, hJ, hFiltered, F, _, hSplit, _, e, he⟩ := h
  letI : Category.{u} J := hJ
  letI : IsFiltered J := hFiltered
  letI : IsIso e := he
  exact UniversallyExact.of_iso (asIso e)
    (UniversallyExact.colimit_of_split F hSplit)

/-- For a short exact sequence of modules, universal exactness is equivalent to
the tensor, equational, finite-free lifting, Hom-surjectivity, and filtered split-colimit
criteria. -/
@[stacks 058K]
theorem tfae (hS : S.ShortExact) :
    ([ S.UniversallyExact
     , tensorRight S
     , equational S
     , finiteFreeSquare S
     , homSurjective S
     , filteredSplitColimit S ] : List Prop).TFAE := by
  tfae_have 1 → 2 := fun h Q ↦ tensorRight_shortExact h Q
  tfae_have 2 → 3 := equational_of_tensorRight
  tfae_have 3 → 4 := finiteFreeSquare_of_equational
  tfae_have 4 → 5 := homSurjective_of_finiteFreeSquare hS
  tfae_have 5 → 6 := filteredSplitColimit_of_homSurjective hS
  tfae_have 6 → 1 := universallyExact_of_filteredSplitColimit
  tfae_finish

end Criteria

section

variable {R : Type u} [CommRing R]
variable {S : ShortComplex (ModuleCat.{v} R)}

/-- If the last term `S.X₃` of a short complex of modules over a commutative ring
is finitely presented, then universal exactness is equivalent to the existence of a splitting. -/
@[stacks 058L]
theorem iff_nonempty_splitting [Module.FinitePresentation R S.X₃] :
    S.UniversallyExact ↔ Nonempty S.Splitting := by
  constructor
  · intro hU
    have hS : S.ShortExact := hU.shortExact
    obtain ⟨n, K, e, hK⟩ := Module.FinitePresentation.exists_fin R S.X₃
    obtain ⟨m, k, hk⟩ := Submodule.fg_iff_exists_fin_generating_family.mp hK
    let d : (Fin m → R) →ₗ[R] (Fin n → R) := Fintype.linearCombination R k
    have hd : LinearMap.range d = K := by
      simpa [d] using (Fintype.range_linearCombination R k).trans hk
    let q : (Fin n → R) →ₗ[R] S.X₃ :=
      e.symm.toLinearMap.comp K.mkQ
    choose y hy using fun i : Fin n => hS.moduleCat_surjective_g (q (Pi.single i 1))
    let psi : (Fin n → R) →ₗ[R] S.X₂ := Fintype.linearCombination R y
    have hgpsi : S.g.hom.comp psi = q := by
      apply LinearMap.ext
      intro x
      change S.g.hom (psi x) = q x
      rw [map_eq_sum_piSingle q x]
      simp [psi, Fintype.linearCombination_apply, hy]
    have hqd : q.comp d = 0 := by
      apply LinearMap.ext
      intro x
      change e.symm (K.mkQ (d x)) = 0
      have hdx : d x ∈ K := by
        rw [← hd]
        exact LinearMap.mem_range_self d x
      change e.symm (Submodule.Quotient.mk (d x)) = 0
      rw [(Submodule.Quotient.mk_eq_zero K).2 hdx]
      simp
    have hcycle (j : Fin m) : S.g.hom (psi (d (Pi.single j 1))) = 0 := by
      calc
        S.g.hom (psi (d (Pi.single j 1))) = q (d (Pi.single j 1)) :=
          LinearMap.congr_fun hgpsi (d (Pi.single j 1))
        _ = 0 := LinearMap.congr_fun hqd (Pi.single j 1)
    choose x hx using fun j => (S.moduleCat_exact_iff.mp hS.exact)
      (psi (d (Pi.single j 1))) (hcycle j)
    let phi : (Fin m → R) →ₗ[R] S.X₁ := Fintype.linearCombination R x
    have hphi_basis (j : Fin m) : phi (Pi.single j 1) = x j := by
      simp [phi, Fintype.linearCombination_apply, Pi.single_apply]
    have hfphi : S.f.hom.comp phi = psi.comp d := by
      apply LinearMap.ext
      intro z
      change S.f.hom (phi z) = psi (d z)
      rw [map_eq_sum_piSingle phi z, map_eq_sum_piSingle d z, map_sum, map_sum]
      apply Finset.sum_congr rfl
      intro j hj
      rw [map_smul, map_smul, hphi_basis, hx]
    obtain ⟨l, hl⟩ := exists_lift_finiteFreeSquare S.f.hom hU.2 d phi psi hfphi
    let psi' : (Fin n → R) →ₗ[R] S.X₂ := psi - S.f.hom.comp l
    have hpsi'd : psi'.comp d = 0 := by
      apply LinearMap.ext
      intro z
      change psi (d z) - S.f.hom (l (d z)) = 0
      have hlz := LinearMap.congr_fun hl z
      change l (d z) = phi z at hlz
      have hfz := LinearMap.congr_fun hfphi z
      change S.f.hom (phi z) = psi (d z) at hfz
      rw [hlz, hfz, sub_self]
    have hgpsi' : S.g.hom.comp psi' = q := by
      apply LinearMap.ext
      intro z
      change S.g.hom (psi z - S.f.hom (l z)) = q z
      rw [map_sub, S.moduleCat_zero_apply, sub_zero]
      exact LinearMap.congr_fun hgpsi z
    have hKker : K ≤ LinearMap.ker psi' := by
      rw [← hd]
      exact LinearMap.range_le_ker_iff.mpr hpsi'd
    let sLin : S.X₃ →ₗ[R] S.X₂ := (K.liftQ psi' hKker).comp e.toLinearMap
    have hsection : S.g.hom.comp sLin = LinearMap.id := by
      apply LinearMap.ext
      intro z
      obtain ⟨z', hz'⟩ := Submodule.mkQ_surjective K (e z)
      change S.g.hom (K.liftQ psi' hKker (e z)) = z
      rw [← hz']
      change S.g.hom (psi' z') = z
      have hg := LinearMap.congr_fun hgpsi' z'
      change S.g.hom (psi' z') = q z' at hg
      rw [hg]
      change e.symm (K.mkQ z') = z
      rw [hz', e.symm_apply_apply]
    let s : S.X₃ ⟶ S.X₂ := ModuleCat.ofHom sLin
    have hs_g : s ≫ S.g = 𝟙 S.X₃ := by
      apply ModuleCat.hom_ext
      simpa [s] using hsection
    exact ⟨ShortComplex.Splitting.ofExactOfSection S hS.exact s hs_g hS.mono_f⟩
  · rintro ⟨s⟩
    refine ⟨s.shortExact, ?_⟩
    intro Q _ _
    have hfr : s.r.hom.comp S.f.hom = LinearMap.id := by
      have hfr' := congrArg ModuleCat.Hom.hom s.f_r
      exact hfr'
    apply LinearMap.injective_of_comp_eq_id (S.f.hom.rTensor Q) (s.r.hom.rTensor Q)
    rw [← LinearMap.rTensor_comp, hfr, LinearMap.rTensor_id]

end

end UniversallyExact

end CategoryTheory.ShortComplex
