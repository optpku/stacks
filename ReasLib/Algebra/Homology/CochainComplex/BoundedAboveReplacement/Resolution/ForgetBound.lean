/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import ReasLib.Algebra.Homology.CochainComplex.Bounded.Fixed.Termwise.Minus
public import ReasLib.Algebra.Homology.CochainComplex.BoundedAboveReplacement.Resolution
public import ReasLib.Algebra.Homology.CochainComplex.BoundedAboveReplacement.Resolution.Variable
public import Mathlib.Tactic.CrossRefAttribute

/-!
# Forgetting the Cutoff of a Bounded-Above Resolution

A fixed-upper-bound resolution canonically determines a variable-bound resolution. The
construction is functorial and retains the underlying complex and comparison map.
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits

universe v u

namespace CochainComplex.StrictlyLE.TermsIn.QuasiIsoFrom

variable {A : Type u} [Category.{v} A] [HasZeroMorphisms A] [CategoryWithHomology A]
  {P : ObjectProperty A} {a : ℤ} {K : CochainComplex A ℤ}

/-- Forget the specified upper cutoff of a fixed-bound left resolution. -/
@[stacks 05T7 "forgetting the cutoff of a bounded-above resolution"]
def forgetBound (R : StrictlyLE.TermsIn.QuasiIsoFrom P a K) :
    Minus.TermsIn.QuasiIsoFrom P K :=
  Minus.TermsIn.QuasiIsoFrom.mk
    ((StrictlyLE.TermsIn.forgetBound P a).obj R.model) R.comparison R.hw

/-- Forgetting the cutoff retains the bundled termwise model. -/
@[simp]
theorem forgetBound_model (R : StrictlyLE.TermsIn.QuasiIsoFrom P a K) :
    R.forgetBound.model = (StrictlyLE.TermsIn.forgetBound P a).obj R.model := sorry

/-- Forgetting the cutoff retains the underlying resolving complex. -/
@[simp]
theorem forgetBound_complex (R : StrictlyLE.TermsIn.QuasiIsoFrom P a K) :
    (R.forgetBound : CochainComplex A ℤ) = R.complex := sorry

/-- Forgetting the cutoff retains the comparison map. -/
@[simp]
theorem forgetBound_comparison (R : StrictlyLE.TermsIn.QuasiIsoFrom P a K) :
    R.forgetBound.comparison = R.comparison := sorry

/-- The forgotten model map satisfies the left-resolution comparison square. -/
theorem forgetBound_hom_comm {R S : StrictlyLE.TermsIn.QuasiIsoFrom P a K}
    (f : R ⟶ S) :
    (Minus.TermsIn.ι P).map ((StrictlyLE.TermsIn.forgetBound P a).map f.f) ≫
        S.forgetBound.comparison =
      R.forgetBound.comparison := sorry

/-- Forget a fixed-bound morphism while retaining its underlying model map. -/
def forgetBoundHom {R S : StrictlyLE.TermsIn.QuasiIsoFrom P a K} (f : R ⟶ S) :
    R.forgetBound ⟶ S.forgetBound where
  f := (StrictlyLE.TermsIn.forgetBound P a).map f.f
  comm := forgetBound_hom_comm f

/-- Forgetting the identity fixed-bound morphism gives the identity. -/
@[simp]
theorem forgetBoundHom_id (R : StrictlyLE.TermsIn.QuasiIsoFrom P a K) :
    forgetBoundHom (𝟙 R) = 𝟙 R.forgetBound := sorry

/-- Forgetting a composite fixed-bound morphism is composition of the forgotten maps. -/
@[simp]
theorem forgetBoundHom_comp {R S T : StrictlyLE.TermsIn.QuasiIsoFrom P a K}
    (f : R ⟶ S) (g : S ⟶ T) :
    forgetBoundHom (f ≫ g) = forgetBoundHom f ≫ forgetBoundHom g := sorry

/-- Functorially forget the specified upper cutoff of fixed-bound left resolutions. -/
@[stacks 05T7 "functorial cutoff-forgetting for bounded-above resolutions"]
def forgetBoundFunctor (P : ObjectProperty A) (a : ℤ) (K : CochainComplex A ℤ) :
    StrictlyLE.TermsIn.QuasiIsoFrom P a K ⥤ Minus.TermsIn.QuasiIsoFrom P K where
  obj R := R.forgetBound
  map f := forgetBoundHom f
  map_id := forgetBoundHom_id
  map_comp := forgetBoundHom_comp

/-- The cutoff-forgetting functor acts on objects by `forgetBound`. -/
@[simp]
theorem forgetBoundFunctor_obj (P : ObjectProperty A) (a : ℤ)
    (K : CochainComplex A ℤ) (R : StrictlyLE.TermsIn.QuasiIsoFrom P a K) :
    (forgetBoundFunctor P a K).obj R = R.forgetBound := sorry

/-- The cutoff-forgetting functor retains the underlying model map. -/
@[simp]
theorem forgetBoundFunctor_map_f (P : ObjectProperty A) (a : ℤ)
    (K : CochainComplex A ℤ) {R S : StrictlyLE.TermsIn.QuasiIsoFrom P a K}
    (f : R ⟶ S) :
    ((forgetBoundFunctor P a K).map f).f =
      (StrictlyLE.TermsIn.forgetBound P a).map f.f := sorry

end CochainComplex.StrictlyLE.TermsIn.QuasiIsoFrom



namespace CochainComplex.Minus.TermsIn.QuasiIsoFrom

variable {A : Type u} [Category.{v} A] [HasZeroMorphisms A] [CategoryWithHomology A]
  {P : ObjectProperty A} {K : CochainComplex A ℤ}

/-- Refine a variable-bound left resolution by an explicitly supplied upper cutoff. -/
@[stacks 05T7 "refining a bounded-above resolution by a specified cutoff"]
def withBound (R : Minus.TermsIn.QuasiIsoFrom P K) (a : ℤ)
    (h : R.complex.IsStrictlyLE a) : StrictlyLE.TermsIn.QuasiIsoFrom P a K :=
  StrictlyLE.TermsIn.QuasiIsoFrom.mk
    ⟨R.complex, ⟨h, R.term_mem⟩⟩ R.comparison R.hw

/-- Refining by a cutoff retains the underlying resolving complex. -/
@[simp]
theorem withBound_complex (R : Minus.TermsIn.QuasiIsoFrom P K) (a : ℤ)
    (h : R.complex.IsStrictlyLE a) :
    (R.withBound a h : CochainComplex A ℤ) = R.complex := sorry

/-- Refining by a cutoff retains the comparison map. -/
@[simp]
theorem withBound_comparison (R : Minus.TermsIn.QuasiIsoFrom P K) (a : ℤ)
    (h : R.complex.IsStrictlyLE a) :
    (R.withBound a h).comparison = R.comparison := sorry

/-- Forgetting an explicitly supplied cutoff recovers the variable-bound resolution. -/
@[simp]
theorem forgetBound_withBound (R : Minus.TermsIn.QuasiIsoFrom P K) (a : ℤ)
    (h : R.complex.IsStrictlyLE a) :
    (R.withBound a h).forgetBound = R := sorry

end CochainComplex.Minus.TermsIn.QuasiIsoFrom


