/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import Mathlib.CategoryTheory.Abelian.GrothendieckCategory.Basic
public import Mathlib.Tactic.CrossRefAttribute
public import ReasLib.Algebra.Homology.CochainComplex.FunctorialApproximation
public import ReasLib.CategoryTheory.Subobject.Injective

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

variable (C : Type u) [Category.{v} C] [HasZeroMorphisms C] [CategoryWithHomology C]

/-- A functorial complex approximation equipped degreewise with concrete factorizations of its
comparison maps through injective subobjects. -/
@[stacks 079N "functorial approximation with injective factors"]
structure WithInjectiveFactors extends toApproximation : FunctorialComplexApproximation C where
  /-- The chosen injective-subobject factorization in degree `n` at the complex `M`. -/
  factor (M : CochainComplex C ℤ) (n : ℤ) :
    Subobject.InjectiveFactor ((toApproximation.ι.app M).f n)

namespace WithInjectiveFactors

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

section Grothendieck

variable [Abelian C]

/-- Lemma 19.12.5: every Grothendieck abelian category admits a functorial monomorphic
quasi-isomorphic complex approximation whose comparison maps factor degreewise through injective
subobjects. -/
@[stacks 079N "bundled existence"]
theorem nonempty [IsGrothendieckAbelian.{w} C] :
    Nonempty (WithInjectiveFactors C) := sorry

/-- The unbundled existential view of an approximation with injective degreewise factors. -/
@[stacks 079N "existential view"]
theorem exists_approximation [IsGrothendieckAbelian.{w} C] :
    ∃ J : FunctorialComplexApproximation C,
      ∀ (M : CochainComplex C ℤ) (n : ℤ),
        ∃ I : Subobject ((J.toFunctor.obj M).X n),
          Injective (I : C) ∧ I.Factors ((J.ι.app M).f n) := sorry

end Grothendieck

end WithInjectiveFactors

end FunctorialComplexApproximation

end CochainComplex
