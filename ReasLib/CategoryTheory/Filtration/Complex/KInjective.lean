/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import ReasLib.CategoryTheory.Filtration.Complex.Quotient
public import Mathlib.Algebra.Homology.HomotopyCategory.KInjective
public import Mathlib.CategoryTheory.Abelian.GrothendieckCategory.Basic
public import Mathlib.Tactic.CrossRefAttribute

/-!
# K-Injective Resolutions of Filtered Complexes

The properties of a filtered K-injective model are split into termwise injectivity,
K-injectivity, and quasi-isomorphism on all canonical filtration views.  A bundled resolution
then supplies these properties as instances, so consumers do not need local instance plumbing.
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

/-- A filtered K-injective resolution coerces to its resolving filtered complex. -/
instance {K : FilteredComplex A} :
    CoeOut (KInjectiveResolution K) (FilteredComplex A) where
  coe R := R.complex

/-- A resolution exposes termwise injectivity to typeclass search. -/
instance {K : FilteredComplex A} (R : KInjectiveResolution K) :
    R.complex.IsTermwiseInjective := R.termwiseInjective

/-- A resolution exposes K-injectivity of all filtration views to typeclass search. -/
instance {K : FilteredComplex A} (R : KInjectiveResolution K) :
    R.complex.IsKInjective := R.kInjective

/-- A resolution exposes its filtrationwise quasi-isomorphism to typeclass search. -/
instance {K : FilteredComplex A} (R : KInjectiveResolution K) :
    IsQuasiIso R.ι := R.quasiIso

end KInjectiveResolution

namespace KInjectiveResolution

/-- Lemma 19.13.7: every filtered complex in a Grothendieck abelian category has a filtered
K-injective resolution compatible with stages, quotients, and subquotients. -/
@[stacks 0BKI]
theorem nonempty [IsGrothendieckAbelian.{w} A]
    (K : FilteredComplex A) : Nonempty (KInjectiveResolution K) := sorry

end KInjectiveResolution

section InstanceChecks

variable {K : FilteredComplex A} (R : KInjectiveResolution K)
  (p q n : ℤ) (hpq : p ≤ q)

#synth Injective (R.complex.underlying.X n)
#synth Injective ((R.complex.stage p).X n)
#synth Injective ((R.complex.quotient p).X n)
#synth Injective ((R.complex.subquotient hpq).X n)
#synth R.complex.underlying.IsKInjective
#synth (R.complex.stage p).IsKInjective
#synth (R.complex.quotient p).IsKInjective
#synth (R.complex.subquotient hpq).IsKInjective
#synth QuasiIso (underlyingMap R.ι)
#synth QuasiIso (stageMap R.ι p)
#synth QuasiIso (quotientMap R.ι p)
#synth QuasiIso (subquotientMap R.ι hpq)

end InstanceChecks

end CategoryTheory.FilteredComplex
