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
    J.factorThru M n ≫ (J.injectiveSubobject M n).arrow = (J.ι.app M).f n := sorry

/-- The comparison component belongs to the chosen injective subobject. -/
theorem factors (J : WithInjectiveFactors C) (M : CochainComplex C ℤ) (n : ℤ) :
    (J.injectiveSubobject M n).Factors ((J.ι.app M).f n) := sorry

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
      (HasFunctorialInjectives.map (f.f (n + 1)))) (by sorry)

/-- The map into the contractible arrangement uses the original embedding and its next differential. -/
noncomputable def injectiveComparison (M : CochainComplex C ℤ) : M ⟶ injectiveComplex M :=
  CochainComplex.ofHom
    (fun n ↦ biprod.lift (HasFunctorialInjectives.ι.app (M.X n))
      (M.d n (n + 1) ≫ HasFunctorialInjectives.ι.app (M.X (n + 1)))) (by sorry)

/-- Naturality of the specified two-component embedding. -/
theorem injectiveComparison_naturality {M N : CochainComplex C ℤ} (f : M ⟶ N) :
    injectiveComparison M ≫ injectiveComplexMap f = f ≫ injectiveComparison N := sorry

/-- The actual cokernel complex of the specified embedding. -/
noncomputable abbrev quotientComplex (M : CochainComplex C ℤ) : CochainComplex C ℤ :=
  cokernel (injectiveComparison M)

/-- The induced map of cokernel complexes comes from the actual commuting square. -/
noncomputable def quotientComplexMap {M N : CochainComplex C ℤ} (f : M ⟶ N) :
    quotientComplex M ⟶ quotientComplex N :=
  cokernel.map (injectiveComparison M) (injectiveComparison N) f
    (injectiveComplexMap f) (injectiveComparison_naturality f)

/-- The shifted cone of the actual cokernel map is the source's approximation. -/
noncomputable def approximationComplex (M : CochainComplex C ℤ) : CochainComplex C ℤ :=
  mappingCocone (cokernel.π (injectiveComparison M))

set_option backward.isDefEq.respectTransparency false in
/-- A map of the specified cokernel arrows acts on their actual mapping cocones. -/
noncomputable def approximationMap {M N : CochainComplex C ℤ} (f : M ⟶ N) :
    approximationComplex M ⟶ approximationComplex N :=
  mappingCocone.lift (cokernel.π (injectiveComparison N))
    (mappingCocone.fst (cokernel.π (injectiveComparison M)) ≫ injectiveComplexMap f)
    ((mappingCocone.snd (cokernel.π (injectiveComparison M))).comp
      (HomComplex.Cochain.ofHom (quotientComplexMap f)) (add_zero (-1))) (by sorry)

/-- The actual mapping-cocone construction is functorial. -/
noncomputable def approximationFunctor : CochainComplex C ℤ ⥤ CochainComplex C ℤ where
  obj := approximationComplex
  map := approximationMap
  map_id := sorry
  map_comp := sorry

set_option backward.isDefEq.respectTransparency false in
/-- The comparison is the native cocone lift of the embedding, whose cokernel composite vanishes. -/
noncomputable def approximationComparison : 𝟭 (CochainComplex C ℤ) ⟶ approximationFunctor where
  app M := mappingCocone.lift (cokernel.π (injectiveComparison M))
    (injectiveComparison M) 0 (by
      simp only [HomComplex.δ_zero, cokernel.condition, HomComplex.Cochain.ofHom_zero, add_zero])
  naturality := sorry

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
    lift_arrow := by sorry }

/-- The concrete source construction using supplied functorial injective embeddings. -/
noncomputable def ofFunctorialInjectives : WithInjectiveFactors C where
  toFunctor := approximationFunctor
  ι := approximationComparison
  mono_app := sorry
  quasiIso_app := sorry
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
