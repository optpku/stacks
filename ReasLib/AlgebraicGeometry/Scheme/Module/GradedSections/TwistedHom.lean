/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import Mathlib.Algebra.Category.ModuleCat.Sheaf.Quasicoherent
public import ReasLib.AlgebraicGeometry.Scheme.Module.GradedSections.Localization

/-!
# Localized graded morphisms between scheme modules

For an invertible module `L`, the morphisms from `F` to the twists of `G` form an
integer-graded module over the section ring of `L`. This file constructs its degree-zero
homogeneous localization and the canonical comparison on the nonvanishing open of a section.
-/

@[expose] public section

open CategoryTheory
open CategoryTheory.MonoidalCategory
open AlgebraicGeometry
open scoped AlgebraicGeometry DirectSum

noncomputable section

universe u v

namespace AlgebraicGeometry.Scheme.Modules.TwistedHom

variable {X : Scheme.{u}}

/-- The degree-`n` homogeneous piece consists of morphisms from `F` to the `n`th invertible
twist of `G`. -/
abbrev degree
    (L : X.Modules) [Invertible L] (F G : X.Modules) (n : ℤ) : Type _ :=
  F ⟶ G ⊗ (L ^⊗ n)

/-- A homogeneous section of a tensor power acts on a twisted morphism by inserting that section
into the target twist. -/
noncomputable def smul
    (L : X.Modules) [Invertible L] (F G : X.Modules) {m : ℕ} {n : ℤ} :
    RingedSpace.GradedSections.degree L m →
      degree L F G n → degree L F G ((m : ℤ) + n) :=
  fun r α ↦
    α ≫ (λ_ (G ⊗ (L ^⊗ n))).inv ≫
      ((RingedSpace.unitIsoTensorUnit X.toRingedSpace).inv ≫
          RingedSpace.topSectionMorphism (RingedSpace.TensorPower.sheaf L m) r ⊗ₘ
        𝟙 (G ⊗ (L ^⊗ n))) ≫
      (RingedSpace.GradedSections.actionIso L G m n).hom

/-- The integer-graded direct sum of morphisms from `F` to the twists of `G`. -/
abbrev graded
    (L : X.Modules) [Invertible L] (F G : X.Modules) : Type _ :=
  ⨁ n : ℤ, degree L F G n

/-- The explicit homogeneous action supplies graded scalar multiplication. -/
noncomputable instance instGSMul
    (L : X.Modules) [Invertible L] (F G : X.Modules) :
    GradedMonoid.GSMul
      (RingedSpace.GradedSections.degree L) (degree L F G) where
  smul := fun r α ↦ smul L F G r α

/-- The graded unit acts trivially on every homogeneous twisted morphism. -/
theorem one_smul
    (L : X.Modules) [Invertible L] (F G : X.Modules)
    (α : GradedMonoid (degree L F G)) :
    (1 : GradedMonoid (RingedSpace.GradedSections.degree L)) • α = α := sorry

/-- Homogeneous multiplication and the action on twisted morphisms are associative. -/
theorem mul_smul
    (L : X.Modules) [Invertible L] (F G : X.Modules)
    (a b : GradedMonoid (RingedSpace.GradedSections.degree L))
    (α : GradedMonoid (degree L F G)) :
    (a * b) • α = a • b • α := sorry

/-- The homogeneous pieces carry the canonical graded multiplicative action. -/
noncomputable instance instGMulAction
    (L : X.Modules) [Invertible L] (F G : X.Modules) :
    GradedMonoid.GMulAction
      (RingedSpace.GradedSections.degree L) (degree L F G) where
  one_smul := one_smul L F G
  mul_smul := mul_smul L F G

/-- The homogeneous action distributes over addition in the morphism variable. -/
theorem smul_add
    (L : X.Modules) [Invertible L] (F G : X.Modules) {m : ℕ} {n : ℤ}
    (r : RingedSpace.GradedSections.degree L m)
    (α β : degree L F G n) :
    smul L F G r (α + β) = smul L F G r α + smul L F G r β := sorry

/-- Every homogeneous section acts trivially on the zero morphism. -/
theorem smul_zero
    (L : X.Modules) [Invertible L] (F G : X.Modules) {m : ℕ} {n : ℤ}
    (r : RingedSpace.GradedSections.degree L m) :
    smul L F G r (0 : degree L F G n) = 0 := sorry

/-- The homogeneous action is additive in the morphism variable. -/
noncomputable instance instGdistribMulAction
    (L : X.Modules) [Invertible L] (F G : X.Modules) :
    DirectSum.GdistribMulAction
      (RingedSpace.GradedSections.degree L) (degree L F G) where
  smul_add := smul_add L F G
  smul_zero := smul_zero L F G

/-- The homogeneous action distributes over addition in the section variable. -/
theorem add_smul
    (L : X.Modules) [Invertible L] (F G : X.Modules) {m : ℕ} {n : ℤ}
    (r t : RingedSpace.GradedSections.degree L m)
    (α : degree L F G n) :
    smul L F G (r + t) α = smul L F G r α + smul L F G t α := sorry

/-- The zero homogeneous section acts trivially. -/
theorem zero_smul
    (L : X.Modules) [Invertible L] (F G : X.Modules) {m : ℕ} {n : ℤ}
    (α : degree L F G n) :
    smul L F G (0 : RingedSpace.GradedSections.degree L m) α = 0 := sorry

/-- The twisted-morphism pieces form a graded module over the tensor-power section ring. -/
noncomputable instance instGmodule
    (L : X.Modules) [Invertible L] (F G : X.Modules) :
    DirectSum.Gmodule
      (RingedSpace.GradedSections.degree L) (degree L F G) where
  add_smul := add_smul L F G
  zero_smul := zero_smul L F G

/-- The degree-`n` internal homogeneous subgroup of the graded twisted-morphism module, for
nonnegative `n`. -/
abbrev grading
    (L : X.Modules) [Invertible L] (F G : X.Modules) (n : ℕ) :
    AddSubgroup (graded L F G) :=
  AddMonoidHom.range (DirectSum.of (degree L F G) (n : ℤ))

/-- Multiplication by a section of degree `i` sends a twisted morphism of degree `j` to degree
`i + j`. -/
theorem smul_mem_grading
    (L : X.Modules) [Invertible L] (F G : X.Modules)
    {i j : ℕ} {r : RingedSpace.GradedSections.ring L}
    {α : graded L F G}
    (hr : r ∈ RingedSpace.GradedSections.grading L i)
    (hα : α ∈ grading L F G j) :
    r • α ∈ grading L F G (i + j) := sorry

/-- The section-ring grading acts compatibly on the nonnegative homogeneous subgroups of twisted
morphisms. -/
noncomputable instance instGradedSMulGrading
    (L : X.Modules) [Invertible L] (F G : X.Modules) :
    SetLike.GradedSMul
      (RingedSpace.GradedSections.grading L) (grading L F G) where
  smul_mem := fun i j r α hr hα ↦
    by
      simpa only [vadd_eq_add] using
        smul_mem_grading L F G (i := i) (j := j) (r := r) (α := α) hr hα

/-- The degree-zero homogeneous localization of the graded twisted-morphism module away from a
degree-one section. -/
abbrev localized
    (L : X.Modules) [Invertible L] (F G : X.Modules) (s : Γ(L, ⊤)) :=
  HomogeneousLocalization.Away.Module.degreeZeroPart
    (RingedSpace.GradedSections.grading L) (grading L F G)
    (Modules.GradedSections.degreeOne L s)

/-- The standard degree-zero localized twisted morphism `α / s^n`. -/
noncomputable def localizedMk
    (L : X.Modules) [Invertible L] (F G : X.Modules) (s : Γ(L, ⊤))
    (n : ℕ) (α : degree L F G (n : ℤ)) :
    localized L F G s :=
  let numerator : grading L F G n :=
    ⟨DirectSum.of (degree L F G) (n : ℤ) α, ⟨α, rfl⟩⟩
  let denominatorDegreeNumerator : grading L F G (n • (1 : ℕ)) := by
    simpa using numerator
  ⟨HomogeneousLocalization.Away.Module.powMkHomogeneous
      (RingedSpace.GradedSections.grading L) (grading L F G)
      (Modules.GradedSections.degreeOne L s) n denominatorDegreeNumerator,
    HomogeneousLocalization.Away.Module.powMkHomogeneous_mem_degreeZeroPart
      (RingedSpace.GradedSections.grading L) (grading L F G)
      (Modules.GradedSections.degreeOne L s) denominatorDegreeNumerator⟩

/-- Every localized twisted morphism admits a standard homogeneous fraction representative. -/
theorem exists_localizedMk_eq
    (L : X.Modules) [Invertible L] (F G : X.Modules) (s : Γ(L, ⊤))
    (z : localized L F G s) :
    ∃ n : ℕ, ∃ α : degree L F G (n : ℤ),
      z = localizedMk L F G s n α := sorry

/-- Additive maps out of the localized twisted-morphism module agree when they agree on every
standard homogeneous fraction. -/
theorem localized_hom_ext
    (L : X.Modules) [Invertible L] (F G : X.Modules) (s : Γ(L, ⊤))
    {A : Type v} [AddCommMonoid A]
    {f g : localized L F G s →+ A}
    (h : ∀ n : ℕ, ∀ α : degree L F G (n : ℤ),
      f (localizedMk L F G s n α) = g (localizedMk L F G s n α)) :
    f = g := sorry

/-- The morphism on the nonvanishing open represented by `α / s^n`, obtained by restricting
`α` and contracting its tensor-power factor. -/
noncomputable def fractionValue
    (L : X.Modules) [Invertible L] (F G : X.Modules) (s : Γ(L, ⊤))
    (n : ℕ) (α : degree L F G (n : ℤ)) :
    F.over (RingedSpace.sectionNonvanishingOpen X.toRingedSpace L
        (RingedSpace.sectionFromTop L s)) ⟶
      G.over (RingedSpace.sectionNonvanishingOpen X.toRingedSpace L
        (RingedSpace.sectionFromTop L s)) :=
  α.over (RingedSpace.sectionNonvanishingOpen X.toRingedSpace L
      (RingedSpace.sectionFromTop L s)) ≫
    Invertible.nonvanishingTwistContraction L G s n

/-- Equal standard localized fractions determine the same restricted and contracted morphism. -/
theorem fractionValue_eq_of_mk_eq
    (L : X.Modules) [Invertible L] (F G : X.Modules) (s : Γ(L, ⊤))
    {n n' : ℕ} {α : degree L F G (n : ℤ)}
    {α' : degree L F G (n' : ℤ)}
    (h : localizedMk L F G s n α = localizedMk L F G s n' α') :
    fractionValue L F G s n α = fractionValue L F G s n' α' := sorry

/-- The comparison function evaluates a localized twisted morphism through a chosen standard
homogeneous fraction representative. -/
noncomputable def localizedComparisonFun
    (L : X.Modules) [Invertible L] (F G : X.Modules) (s : Γ(L, ⊤)) :
    localized L F G s →
      (F.over (RingedSpace.sectionNonvanishingOpen X.toRingedSpace L
          (RingedSpace.sectionFromTop L s)) ⟶
        G.over (RingedSpace.sectionNonvanishingOpen X.toRingedSpace L
          (RingedSpace.sectionFromTop L s))) :=
  fun z ↦
    let h := (HomogeneousLocalization.Away.Module.mem_degreeZeroPart_iff
      (RingedSpace.GradedSections.grading L) (grading L F G)
      (Modules.GradedSections.degreeOne L s)).mp z.2
    let representative :
        Σ n : ℕ, grading L F G (n • (1 : ℕ)) :=
      ⟨Classical.choose h, Classical.choose (Classical.choose_spec h)⟩
    let α : degree L F G (representative.1 : ℤ) := by
      simpa using Classical.choose representative.2.2
    fractionValue L F G s representative.1 α

/-- The localized comparison function sends zero to the zero morphism. -/
theorem localizedComparisonFun_map_zero
    (L : X.Modules) [Invertible L] (F G : X.Modules) (s : Γ(L, ⊤)) :
    localizedComparisonFun L F G s 0 = 0 := sorry

/-- The localized comparison function preserves addition. -/
theorem localizedComparisonFun_map_add
    (L : X.Modules) [Invertible L] (F G : X.Modules) (s : Γ(L, ⊤))
    (x y : localized L F G s) :
    localizedComparisonFun L F G s (x + y) =
      localizedComparisonFun L F G s x +
        localizedComparisonFun L F G s y := sorry

/-- The canonical additive comparison from localized twisted morphisms to morphisms between the
restrictions on the nonvanishing open. -/
noncomputable def localizedComparison
    (L : X.Modules) [Invertible L]
    (F G : X.Modules) [F.IsQuasicoherent] [G.IsQuasicoherent]
    (s : Γ(L, ⊤)) :
    localized L F G s →+
      (F.over (RingedSpace.sectionNonvanishingOpen X.toRingedSpace L
          (RingedSpace.sectionFromTop L s)) ⟶
        G.over (RingedSpace.sectionNonvanishingOpen X.toRingedSpace L
          (RingedSpace.sectionFromTop L s))) where
  toFun := localizedComparisonFun L F G s
  map_zero' := localizedComparisonFun_map_zero L F G s
  map_add' := localizedComparisonFun_map_add L F G s

/-- On a standard fraction, the localized comparison restricts its numerator and contracts the
twist by the inverse power of the nonvanishing section. -/
theorem localizedComparison_apply_mk
    (L : X.Modules) [Invertible L]
    (F G : X.Modules) [F.IsQuasicoherent] [G.IsQuasicoherent]
    (s : Γ(L, ⊤)) (n : ℕ) (α : degree L F G (n : ℤ)) :
    localizedComparison L F G s (localizedMk L F G s n α) =
      fractionValue L F G s n α := sorry

end AlgebraicGeometry.Scheme.Modules.TwistedHom
