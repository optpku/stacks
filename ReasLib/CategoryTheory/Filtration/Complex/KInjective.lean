/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.CategoryTheory.Filtration.Complex.Quotient
public import Mathlib.Algebra.Homology.HomotopyCategory.KInjective
public import Mathlib.CategoryTheory.Abelian.GrothendieckCategory.Basic
public import Mathlib.Tactic.CrossRefAttribute

/-!
# K-Injective Resolutions of Filtered Complexes

The properties of a filtered K-injective model are split into termwise injectivity,
K-injectivity, and quasi-isomorphism on all canonical filtration views. A resolution records
the resolving complex, its comparison morphism, and explicit proofs of these properties.
-/

@[expose] public section

open CategoryTheory

noncomputable section

universe w v u

namespace CategoryTheory.FilteredComplex

variable {A : Type u} [Category.{v} A] [Abelian A]

/-- Termwise injectivity of the underlying complex and all stage, quotient, and subquotient
complexes of a filtered complex. -/
@[stacks 0BKI "termwise injective filtered complex"]
class IsTermwiseInjective (J : FilteredComplex A) : Prop where
  /-- The underlying complex is termwise injective. -/
  underlying : ∀ n : ℤ, Injective (J.underlying.X n)
  /-- Every filtration-stage complex is termwise injective. -/
  stage : ∀ p n : ℤ, Injective ((J.stage p).X n)
  /-- Every quotient by a filtration stage is termwise injective. -/
  quotient : ∀ p n : ℤ, Injective ((J.quotient p).X n)
  /-- Every quotient of two comparable filtration stages is termwise injective. -/
  subquotient : ∀ {p q : ℤ} (hpq : p ≤ q) (n : ℤ),
    Injective ((J.subquotient hpq).X n)

/-- K-injectivity of the underlying complex and all stage, quotient, and subquotient complexes
of a filtered complex. -/
@[stacks 0BKI "K-injective filtered complex"]
class IsKInjective (J : FilteredComplex A) : Prop where
  /-- The underlying complex is K-injective. -/
  underlying : J.underlying.IsKInjective
  /-- Every filtration-stage complex is K-injective. -/
  stage : ∀ p : ℤ, (J.stage p).IsKInjective
  /-- Every quotient by a filtration stage is K-injective. -/
  quotient : ∀ p : ℤ, (J.quotient p).IsKInjective
  /-- Every quotient of two comparable filtration stages is K-injective. -/
  subquotient : ∀ {p q : ℤ} (hpq : p ≤ q), (J.subquotient hpq).IsKInjective

/-- A filtered-complex morphism is a quasi-isomorphism on the underlying complex and on every
stage, quotient, and subquotient. -/
@[stacks 0BKI "filtrationwise quasi-isomorphism"]
class IsQuasiIso {K J : FilteredComplex A} (f : K ⟶ J) : Prop where
  /-- The underlying cochain-complex map is a quasi-isomorphism. -/
  underlying : QuasiIso (underlyingMap f)
  /-- Every induced map of filtration stages is a quasi-isomorphism. -/
  stage : ∀ p : ℤ, QuasiIso (stageMap f p)
  /-- Every induced map on quotients by a filtration stage is a quasi-isomorphism. -/
  quotient : ∀ p : ℤ, QuasiIso (quotientMap f p)
  /-- Every induced map on filtration subquotients is a quasi-isomorphism. -/
  subquotient : ∀ {p q : ℤ} (hpq : p ≤ q), QuasiIso (subquotientMap f hpq)

attribute [instance]
  IsTermwiseInjective.underlying IsTermwiseInjective.stage
  IsTermwiseInjective.quotient IsTermwiseInjective.subquotient
  IsKInjective.underlying IsKInjective.stage IsKInjective.quotient IsKInjective.subquotient
  IsQuasiIso.underlying IsQuasiIso.stage IsQuasiIso.quotient IsQuasiIso.subquotient

/-- A K-injective resolution of a filtered complex, compatible with every canonical filtration
view. -/
@[stacks 0BKI "filtered K-injective resolution"]
structure KInjectiveResolution (K : FilteredComplex A) where
  /-- The resolving filtered complex. -/
  complex : FilteredComplex A
  /-- The comparison morphism from the original filtered complex. -/
  ι : K ⟶ complex
  /-- All terms in the canonical filtration views are injective. -/
  termwiseInjective : complex.IsTermwiseInjective
  /-- All canonical filtration views are K-injective complexes. -/
  kInjective : complex.IsKInjective
  /-- The comparison is a quasi-isomorphism on every canonical filtration view. -/
  quasiIso : IsQuasiIso ι

namespace KInjectiveResolution

/-- The comparison morphism of a filtered K-injective resolution as an arrow of filtered
complexes. -/
def toArrow {K : FilteredComplex A} (R : KInjectiveResolution K) :
    Arrow (FilteredComplex A) :=
  Arrow.mk R.ι

/-- The morphism of the resolution arrow is the resolution comparison morphism. -/
theorem toArrow_hom {K : FilteredComplex A} (R : KInjectiveResolution K) :
    R.toArrow.hom = R.ι := rfl

/-- Every filtered complex in a Grothendieck abelian category has a filtered
K-injective resolution compatible with stages, quotients, and subquotients. -/
@[stacks 0BKI]
theorem nonempty [IsGrothendieckAbelian.{w} A]
    (K : FilteredComplex A) : Nonempty (KInjectiveResolution K) := sorry

end KInjectiveResolution

end CategoryTheory.FilteredComplex
