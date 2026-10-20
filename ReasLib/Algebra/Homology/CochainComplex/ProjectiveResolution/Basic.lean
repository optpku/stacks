module

public import Mathlib.Algebra.Homology.HomotopyCategory.KProjective
public import Mathlib.Algebra.Homology.Factorizations.CM5a
public import Mathlib.Algebra.Homology.Refinements
public import Mathlib.CategoryTheory.Preadditive.Projective.Basic
public import Mathlib.Tactic.CrossRefAttribute
public import ReasLib.Algebra.Homology.CochainComplex.BoundedAboveReplacement.Resolution.Variable

@[expose] public section

/-!
# Projective Resolutions of Cochain Complexes: Basic API

This module specializes `CochainComplex.Minus.TermsIn` to projective objects, defines projective
resolutions of cochain complexes, and registers their canonical K-projective instances.
-/

open CategoryTheory
open CategoryTheory.Limits
open CategoryTheory.ObjectProperty

universe v u

namespace CochainComplex

variable {𝒜 : Type u} [Category.{v} 𝒜] [Abelian 𝒜]

/-- The bounded-above cochain complexes whose terms are projective objects. -/
@[stacks 0643 "bounded-above complexes of projective objects"]
abbrev ProjectiveMinus (𝒜 : Type u) [Category.{v} 𝒜] [Abelian 𝒜] :=
  CochainComplex.Minus.TermsIn (isProjective 𝒜)

namespace ProjectiveMinus

/-- The canonical inclusion of bounded-above termwise-projective cochain
complexes into all cochain complexes. -/
@[stacks 0643 "inclusion of bounded-above projective complexes"]
abbrev ι (𝒜 : Type u) [Category.{v} 𝒜] [Abelian 𝒜] :
    ProjectiveMinus 𝒜 ⥤ CochainComplex 𝒜 ℤ :=
  Minus.TermsIn.ι (isProjective 𝒜)

end ProjectiveMinus

namespace Minus.TermsIn

/-- A bounded-above cochain complex of projective objects is K-projective. -/
@[stacks 0647]
instance instIsKProjective (P : ProjectiveMinus 𝒜) :
    IsKProjective (P : CochainComplex 𝒜 ℤ) := by
  obtain ⟨bound, boundInstance⟩ := P.obj.property
  have termsProjective (degree : ℤ) :
      Projective ((P : CochainComplex 𝒜 ℤ).X degree) := P.property degree
  exact isKProjective_of_projective _ bound

end Minus.TermsIn

/-- A projective resolution is a left resolution along the inclusion of
bounded-above termwise-projective complexes and quasi-isomorphisms. -/
@[stacks 0643 "bounded-above projective left resolution"]
abbrev ProjectiveResolution (K : CochainComplex 𝒜 ℤ) :=
  Minus.TermsIn.QuasiIsoFrom (isProjective 𝒜) K

namespace ProjectiveResolution

/-- Construct a projective resolution from an explicit bounded-above projective complex and
quasi-isomorphism. -/
def mk {K : CochainComplex 𝒜 ℤ} (P : ProjectiveMinus 𝒜)
    (f : (P : CochainComplex 𝒜 ℤ) ⟶ K) (hf : QuasiIso f) : ProjectiveResolution K :=
  Minus.TermsIn.QuasiIsoFrom.mk P f hf

/-- The bounded-above projective model underlying a projective resolution. -/
abbrev model {K : CochainComplex 𝒜 ℤ} (P : ProjectiveResolution K) : ProjectiveMinus 𝒜 :=
  Minus.TermsIn.QuasiIsoFrom.model P

/-- The cochain complex underlying a projective resolution. -/
abbrev complex {K : CochainComplex 𝒜 ℤ} (P : ProjectiveResolution K) :
    CochainComplex 𝒜 ℤ :=
  Minus.TermsIn.QuasiIsoFrom.complex P

/-- The resolving complex in a projective resolution is K-projective. -/
@[stacks 0647 "projective resolutions are K-projective"]
instance instIsKProjective {K : CochainComplex 𝒜 ℤ} (P : ProjectiveResolution K) :
    IsKProjective P.complex := Minus.TermsIn.instIsKProjective P.model

/-- Forgetting the bundled projective model gives the resolving cochain complex. -/
theorem model_coe {K : CochainComplex 𝒜 ℤ} (P : ProjectiveResolution K) :
    (P.model : CochainComplex 𝒜 ℤ) = P.complex := sorry

/-- The comparison map from a projective model to the original complex. -/
abbrev π {K : CochainComplex 𝒜 ℤ} (P : ProjectiveResolution K) :
    P.complex ⟶ K :=
  Minus.TermsIn.QuasiIsoFrom.comparison P

/-- The comparison map of a projective resolution is a quasi-isomorphism. -/
theorem quasiIso {K : CochainComplex 𝒜 ℤ} (P : ProjectiveResolution K) :
    QuasiIso P.π := P.hw

attribute [instance] ProjectiveResolution.quasiIso

/-- The morphism of bounded-above projective models underlying a resolution morphism. -/
abbrev modelHom {K : CochainComplex 𝒜 ℤ} {P Q : ProjectiveResolution K} (f : P ⟶ Q) :
    P.model ⟶ Q.model :=
  Minus.TermsIn.QuasiIsoFrom.modelHom f

/-- Morphisms of projective resolutions are determined by their morphisms of bundled models. -/
@[ext]
theorem hom_ext {K : CochainComplex 𝒜 ℤ} {P Q : ProjectiveResolution K}
    {f g : P ⟶ Q} (h : modelHom f = modelHom g) : f = g := sorry

/-- The cochain map underlying a morphism of projective resolutions. -/
abbrev hom {K : CochainComplex 𝒜 ℤ} {P Q : ProjectiveResolution K} (f : P ⟶ Q) :
    P.complex ⟶ Q.complex :=
  Minus.TermsIn.QuasiIsoFrom.hom f

/-- The cochain map of a resolution morphism is induced by its projective-model morphism. -/
@[simp]
theorem hom_eq_map_modelHom {K : CochainComplex 𝒜 ℤ}
    {P Q : ProjectiveResolution K} (f : P ⟶ Q) :
    hom f = (ProjectiveMinus.ι 𝒜).map (modelHom f) := sorry

/-- The identity resolution morphism induces the identity projective-model morphism. -/
@[simp]
theorem id_modelHom {K : CochainComplex 𝒜 ℤ} (P : ProjectiveResolution K) :
    modelHom (𝟙 P) = 𝟙 P.model := sorry

/-- Composition of resolution morphisms induces composition of projective-model morphisms. -/
@[simp]
theorem comp_modelHom {K : CochainComplex 𝒜 ℤ} {P Q R : ProjectiveResolution K}
    (f : P ⟶ Q) (g : Q ⟶ R) :
    modelHom (f ≫ g) = modelHom f ≫ modelHom g := sorry

/-- The identity resolution morphism induces the identity cochain map. -/
@[simp]
theorem id_hom {K : CochainComplex 𝒜 ℤ} (P : ProjectiveResolution K) :
    hom (𝟙 P) = 𝟙 P.complex := sorry

/-- Composition of resolution morphisms induces composition of cochain maps. -/
@[simp]
theorem comp_hom {K : CochainComplex 𝒜 ℤ} {P Q R : ProjectiveResolution K}
    (f : P ⟶ Q) (g : Q ⟶ R) :
    hom (f ≫ g) = hom f ≫ hom g := sorry

/-- A morphism of projective resolutions commutes with the comparison maps. -/
@[reassoc]
theorem π_naturality {K : CochainComplex 𝒜 ℤ} {P Q : ProjectiveResolution K} (f : P ⟶ Q) :
    hom f ≫ Q.π = P.π := sorry

/-- The functor selecting the bounded-above projective model of a resolution. -/
abbrev modelFunctor (K : CochainComplex 𝒜 ℤ) :
    ProjectiveResolution K ⥤ ProjectiveMinus 𝒜 :=
  Minus.TermsIn.QuasiIsoFrom.modelFunctor (isProjective 𝒜) K

/-- The projective-model functor returns the bundled model of a resolution. -/
@[simp]
theorem modelFunctor_obj {K : CochainComplex 𝒜 ℤ} (P : ProjectiveResolution K) :
    (modelFunctor K).obj P = P.model := sorry

/-- The projective-model functor returns the model morphism of a resolution morphism. -/
@[simp]
theorem modelFunctor_map {K : CochainComplex 𝒜 ℤ}
    {P Q : ProjectiveResolution K} (f : P ⟶ Q) :
    (modelFunctor K).map f = modelHom f := sorry

/-- The functor selecting the underlying cochain complex of a projective resolution. -/
abbrev complexFunctor (K : CochainComplex 𝒜 ℤ) :
    ProjectiveResolution K ⥤ CochainComplex 𝒜 ℤ :=
  Minus.TermsIn.QuasiIsoFrom.complexFunctor (isProjective 𝒜) K

/-- The underlying-complex functor returns the resolving complex. -/
@[simp]
theorem complexFunctor_obj {K : CochainComplex 𝒜 ℤ} (P : ProjectiveResolution K) :
    (complexFunctor K).obj P = P.complex := sorry

/-- The underlying-complex functor returns the cochain map of a resolution morphism. -/
@[simp]
theorem complexFunctor_map {K : CochainComplex 𝒜 ℤ}
    {P Q : ProjectiveResolution K} (f : P ⟶ Q) :
    (complexFunctor K).map f = hom f := sorry

/-- Forgetting the bundled projective models identifies the model and complex functors. -/
theorem modelFunctor_comp_ι (K : CochainComplex 𝒜 ℤ) :
    modelFunctor K ⋙ ProjectiveMinus.ι 𝒜 = complexFunctor K := sorry

/-- The projective-resolution comparisons form a natural transformation. -/
abbrev πNatTrans (K : CochainComplex 𝒜 ℤ) :
    complexFunctor K ⟶ (Functor.const (ProjectiveResolution K)).obj K :=
  Minus.TermsIn.QuasiIsoFrom.comparisonNatTrans (isProjective 𝒜) K

/-- Evaluating the projective-resolution comparison transformation gives its comparison map. -/
@[simp]
theorem πNatTrans_app {K : CochainComplex 𝒜 ℤ} (P : ProjectiveResolution K) :
    (πNatTrans K).app P = P.π := sorry

/-- The named constructor retains the supplied bundled projective model. -/
@[simp]
theorem mk_model {K : CochainComplex 𝒜 ℤ} (P : ProjectiveMinus 𝒜)
    (f : (P : CochainComplex 𝒜 ℤ) ⟶ K) (hf : QuasiIso f) :
    (mk P f hf).model = P := sorry

/-- The named constructor retains the underlying complex of the supplied model. -/
@[simp]
theorem mk_complex {K : CochainComplex 𝒜 ℤ} (P : ProjectiveMinus 𝒜)
    (f : (P : CochainComplex 𝒜 ℤ) ⟶ K) (hf : QuasiIso f) :
    (mk P f hf).complex = (P : CochainComplex 𝒜 ℤ) := sorry

/-- The named constructor retains the supplied comparison map. -/
@[simp]
theorem mk_π {K : CochainComplex 𝒜 ℤ} (P : ProjectiveMinus 𝒜)
    (f : (P : CochainComplex 𝒜 ℤ) ⟶ K) (hf : QuasiIso f) :
    (mk P f hf).π = f := sorry

/-- Projective resolutions exist exactly when explicit bounded-above projective comparison data
exist. -/
theorem nonempty_iff {K : CochainComplex 𝒜 ℤ} :
    Nonempty (ProjectiveResolution K) ↔
      ∃ (P : ProjectiveMinus 𝒜) (f : (P : CochainComplex 𝒜 ℤ) ⟶ K), QuasiIso f := sorry

end ProjectiveResolution

namespace Minus.TermsIn.Bounded.QuasiIso

variable {a : ℤ} {K Q : CochainComplex 𝒜 ℤ} {π : Q ⟶ K}

/-- Package a bounded-above quasi-isomorphism from a cochain complex of projective objects as a
cochain-complex projective resolution. -/
@[stacks 0643]
abbrev toProjectiveResolution
    (hπ : Minus.TermsIn.Bounded.QuasiIso (isProjective 𝒜) a K Q π) :
    ProjectiveResolution K :=
  ProjectiveResolution.mk hπ.toMinus π hπ.quasiIso

end Minus.TermsIn.Bounded.QuasiIso

namespace Minus.TermsIn.Bounded.QuasiIso.Epi

variable {a : ℤ} {K Q : CochainComplex 𝒜 ℤ} {π : Q ⟶ K}

/-- Package a termwise-epimorphic bounded-above quasi-isomorphism from a
cochain complex of projective objects as a cochain-complex projective resolution. -/
@[stacks 0643]
abbrev toProjectiveResolution
    (hπ : Minus.TermsIn.Bounded.QuasiIso.Epi (isProjective 𝒜) a K Q π) :
    ProjectiveResolution K :=
  hπ.toQuasiIso.toProjectiveResolution

end Minus.TermsIn.Bounded.QuasiIso.Epi

namespace ProjectiveResolution

/-- The resolving complex in a projective resolution is bounded above. -/
theorem minus {K : CochainComplex 𝒜 ℤ} (P : ProjectiveResolution K) :
    CochainComplex.minus 𝒜 P.complex := P.model.obj.property

/-- The resolving complex in a projective resolution is zero in all sufficiently high degrees. -/
theorem exists_isStrictlyLE {K : CochainComplex 𝒜 ℤ} (P : ProjectiveResolution K) :
    ∃ d : ℤ, P.complex.IsStrictlyLE d := P.model.obj.property

/-- Each term of the resolving complex in a projective resolution is projective. -/
theorem projective {K : CochainComplex 𝒜 ℤ} (P : ProjectiveResolution K) (n : ℤ) :
    Projective (P.complex.X n) := P.model.property n

attribute [instance] ProjectiveResolution.projective

/-- A cochain complex admitting a bounded-above projective
resolution has zero homology in all sufficiently positive degrees. -/
@[stacks 0645]
theorem eventually_isZero_homology {K : CochainComplex 𝒜 ℤ}
    (P : ProjectiveResolution K) :
    ∃ b : ℤ, ∀ n : ℤ, b < n → IsZero (K.homology n) := sorry

/-- A cochain complex with homology zero in sufficiently
positive degrees admits a bounded-above projective resolution. -/
@[stacks 0646]
theorem nonempty_of_eventually_isZero_homology [EnoughProjectives 𝒜]
    {K : CochainComplex 𝒜 ℤ}
    (hK : ∃ b : ℤ, ∀ n : ℤ, b < n → IsZero (K.homology n)) :
    Nonempty (ProjectiveResolution K) := sorry

private theorem mono_at_lower_bound_of_quasiIso
    {Source Target : CochainComplex 𝒜 ℤ} (comparison : Source ⟶ Target)
    (bound : ℤ) [Source.IsStrictlyGE bound] [QuasiIso comparison]
    [Mono (comparison.f (bound + 1))] : Mono (comparison.f bound) := by
  apply (Preadditive.mono_iff_cancel_zero _).mpr
  intro object morphism equality
  have cycleCondition : morphism ≫ Source.d bound (bound + 1) = 0 := by
    apply (cancel_mono (comparison.f (bound + 1))).mp
    rw [zero_comp, Category.assoc, ← comparison.comm bound (bound + 1),
      ← Category.assoc, equality, zero_comp]
  obtain ⟨refinedObject, cover, coverEpi, lift, liftCondition⟩ :=
    (HomologicalComplex.mono_homologyMap_iff_up_to_refinements comparison
      (bound - 1) bound (bound + 1) (by simp) (by simp)).mp
        inferInstance morphism cycleCondition 0 (by simpa using equality)
  have previousZero := Source.isZero_of_isStrictlyGE bound (bound - 1) (by omega)
  apply (cancel_epi cover).mp
  rw [previousZero.eq_of_tgt lift 0, zero_comp] at liftCondition
  simpa only [comp_zero] using liftCondition

private theorem exists_injective_with_termwise_mono [EnoughInjectives 𝒜]
    (Source : CochainComplex 𝒜 ℤ) (bound : ℤ) [Source.IsStrictlyGE bound] :
    ∃ (Target : CochainComplex 𝒜 ℤ) (comparison : Source ⟶ Target),
      Target.IsStrictlyGE bound ∧ QuasiIso comparison ∧
        (∀ degree : ℤ, Injective (Target.X degree)) ∧
        ∀ degree : ℤ, Mono (comparison.f degree) := by
  obtain ⟨Target, comparison, comparisonMono, comparisonQuasiIso, termsInjective,
      targetBound⟩ := Plus.modelCategoryQuillen.exists_mono_quasiIso_injective
        Source (bound - 1) bound (by omega)
  have targetCohomologyBound : Target.IsGE bound := by
    rw [CochainComplex.isGE_iff]
    intro degree inequality
    exact (exactAt_iff_of_quasiIsoAt comparison degree).mp
      (Source.exactAt_of_isGE bound degree inequality)
  have truncationQuasiIso : QuasiIso (Target.πTruncGE bound) :=
    (Target.quasiIso_πTruncGE_iff bound).mpr targetCohomologyBound
  have bottomInjective : Injective (Target.opcycles bound) :=
    Target.injective_opcycles (bound - 1) bound
      (Target.exactAt_of_isGE bound (bound - 1))
  let truncatedComparison := comparison ≫ Target.πTruncGE bound
  have truncationIsIso (degree : ℤ) (inequality : bound < degree) :
      IsIso ((Target.πTruncGE bound).f degree) := by
    dsimp only [CochainComplex.πTruncGE, CochainComplex.truncGE,
      HomologicalComplex.πTruncGE, HomologicalComplex.truncGE]
    rw [(ComplexShape.embeddingUpIntGE bound).isIso_liftExtend_f_iff _ _
      (show (ComplexShape.embeddingUpIntGE bound).f (degree - bound).natAbs = degree by
        change bound + (degree - bound).natAbs = degree
        rw [Int.natAbs_of_nonneg (by omega)]
        omega)]
    apply Target.isIso_restrictionToTruncGE'
    rw [ComplexShape.boundaryGE_embeddingUpIntGE_iff, Int.natAbs_eq_zero]
    omega
  refine ⟨Target.truncGE bound, truncatedComparison, inferInstance, inferInstance,
    fun degree => ?_, fun degree => ?_⟩
  · obtain inequality | equality | inequality := lt_trichotomy degree bound
    · exact (Target.truncGE bound).isZero_of_isStrictlyGE bound degree inequality |>.injective
    · subst degree
      exact Injective.of_iso (Target.truncGEXIsoOpcycles bound).symm bottomInjective
    · exact Injective.of_iso (Target.truncGEXIso bound degree inequality).symm
        (termsInjective degree)
  · obtain inequality | equality | inequality := lt_trichotomy degree bound
    · exact (Source.isZero_of_isStrictlyGE bound degree inequality).mono _
    · subst degree
      have nextTruncationIsIso := truncationIsIso (bound + 1) (by omega)
      have nextMono : Mono (truncatedComparison.f (bound + 1)) := by
        dsimp [truncatedComparison]
        infer_instance
      exact mono_at_lower_bound_of_quasiIso truncatedComparison bound
    · dsimp [truncatedComparison]
      have degreeTruncationIsIso := truncationIsIso degree inequality
      infer_instance

private theorem quasiIso_of_op_inverse
    {Source Target : CochainComplex 𝒜ᵒᵖ ℤ} (comparison : Source ⟶ Target)
    [QuasiIso comparison] :
    QuasiIso ((opEquivalence 𝒜).inverse.map comparison).unop := by
  rw [quasiIso_iff]
  intro degree
  rw [quasiIsoAt_iff' _ (degree - 1) degree (degree + 1) (by simp) (by simp)]
  change ShortComplex.QuasiIso (ShortComplex.unopMap
    ((HomologicalComplex.shortComplexFunctor' 𝒜ᵒᵖ (ComplexShape.up ℤ)
      (-(degree + 1)) (-degree) (-(degree - 1))).map comparison))
  have degreeQuasiIso :=
    (quasiIsoAt_iff' comparison (-(degree + 1)) (-degree) (-(degree - 1))
      (by simp; omega) (by simp; omega)).mp inferInstance
  exact ShortComplex.quasiIso_unopMap _

/-- A cochain complex zero above `a` admits a projective
resolution whose source is zero above `a` and whose comparison is termwise
epimorphic. -/
@[stacks 0646]
theorem exists_strictlyLE_with_termwise_epi [EnoughProjectives 𝒜]
    {K : CochainComplex 𝒜 ℤ}
    (a : ℤ) (hK : K.IsStrictlyLE a) :
    ∃ P : ProjectiveResolution K,
      P.complex.IsStrictlyLE a ∧ ∀ n : ℤ, Epi (P.π.f n) := by
  let oppositeSource := (opEquivalence 𝒜).functor.obj (Opposite.op K)
  have oppositeSourceBound : oppositeSource.IsStrictlyGE (-a) := by
    rw [isStrictlyGE_iff]
    intro degree inequality
    exact (K.isZero_of_isStrictlyLE a (-degree) (by omega)).op
  obtain ⟨injectiveComplex, injectiveComparison, injectiveBound, comparisonQuasiIso,
      termsInjective, termsMono⟩ :=
    exists_injective_with_termwise_mono oppositeSource (-a)
  let resolvingComplex := ((opEquivalence 𝒜).inverse.obj injectiveComplex).unop
  let comparison := ((opEquivalence 𝒜).inverse.map injectiveComparison).unop ≫
    ((opEquivalence 𝒜).unitIso.app (Opposite.op K)).unop.hom
  have resolvingBound : resolvingComplex.IsStrictlyLE a := by
    rw [isStrictlyLE_iff]
    intro degree inequality
    exact (injectiveComplex.isZero_of_isStrictlyGE (-a) (-degree) (by omega)).unop
  have termsProjective (degree : ℤ) : Projective (resolvingComplex.X degree) := by
    have termInjective := termsInjective (-degree)
    change Projective (injectiveComplex.X (-degree)).unop
    infer_instance
  have inverseQuasiIso := quasiIso_of_op_inverse injectiveComparison
  have comparisonQuasiIso : QuasiIso comparison := by
    dsimp only [comparison]
    infer_instance
  let model : ProjectiveMinus 𝒜 :=
    ⟨⟨resolvingComplex, ⟨a, resolvingBound⟩⟩, termsProjective⟩
  refine ⟨mk model comparison comparisonQuasiIso, resolvingBound, fun degree => ?_⟩
  have termMono := termsMono (-degree)
  change Epi (comparison.f degree)
  dsimp only [comparison, HomologicalComplex.comp_f]
  have inverseEpi : Epi
      ((((opEquivalence 𝒜).inverse.map injectiveComparison).unop).f degree) := by
    change Epi (injectiveComparison.f (-degree)).unop
    infer_instance
  infer_instance

end ProjectiveResolution

end CochainComplex
