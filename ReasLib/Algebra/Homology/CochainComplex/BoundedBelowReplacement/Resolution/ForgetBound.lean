/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import ReasLib.Algebra.Homology.CochainComplex.Bounded.Fixed.Termwise.Plus
public import ReasLib.Algebra.Homology.CochainComplex.BoundedBelowReplacement.Resolution
public import ReasLib.Algebra.Homology.CochainComplex.BoundedBelowReplacement.Resolution.Variable
public import Mathlib.Tactic.CrossRefAttribute

/-!
# Forgetting the Cutoff of a Bounded-Below Resolution

A fixed-lower-bound resolution canonically determines a variable-bound resolution. The
construction is functorial and retains the underlying complex and comparison map.
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits

universe v u

namespace CochainComplex.StrictlyGE.TermsIn.QuasiIsoTo

variable {A : Type u} [Category.{v} A] [HasZeroMorphisms A] [CategoryWithHomology A]
  {P : ObjectProperty A} {a : ℤ} {K : CochainComplex A ℤ}

/-- Forget the specified lower cutoff of a fixed-bound right resolution. -/
@[stacks 05T6 "forgetting the cutoff of a bounded-below resolution"]
def forgetBound (R : StrictlyGE.TermsIn.QuasiIsoTo P a K) :
    Plus.TermsIn.QuasiIsoTo P K :=
  Plus.TermsIn.QuasiIsoTo.mk
    ((StrictlyGE.TermsIn.forgetBound P a).obj R.model) R.comparison R.hw

/-- Forgetting the cutoff retains the bundled termwise model. -/
@[simp]
theorem forgetBound_model (R : StrictlyGE.TermsIn.QuasiIsoTo P a K) :
    R.forgetBound.model = (StrictlyGE.TermsIn.forgetBound P a).obj R.model := sorry

/-- Forgetting the cutoff retains the underlying resolving complex. -/
@[simp]
theorem forgetBound_complex (R : StrictlyGE.TermsIn.QuasiIsoTo P a K) :
    (R.forgetBound : CochainComplex A ℤ) = R.complex := sorry

/-- Forgetting the cutoff retains the comparison map. -/
@[simp]
theorem forgetBound_comparison (R : StrictlyGE.TermsIn.QuasiIsoTo P a K) :
    R.forgetBound.comparison = R.comparison := sorry

/-- The forgotten model map satisfies the right-resolution comparison square. -/
theorem forgetBound_hom_comm {R S : StrictlyGE.TermsIn.QuasiIsoTo P a K}
    (f : R ⟶ S) :
    R.forgetBound.comparison ≫
        (Plus.TermsIn.ι P).map ((StrictlyGE.TermsIn.forgetBound P a).map f.f) =
      S.forgetBound.comparison := sorry

/-- Forget a fixed-bound morphism while retaining its underlying model map. -/
def forgetBoundHom {R S : StrictlyGE.TermsIn.QuasiIsoTo P a K} (f : R ⟶ S) :
    R.forgetBound ⟶ S.forgetBound where
  f := (StrictlyGE.TermsIn.forgetBound P a).map f.f
  comm := forgetBound_hom_comm f

/-- Forgetting the identity fixed-bound morphism gives the identity. -/
@[simp]
theorem forgetBoundHom_id (R : StrictlyGE.TermsIn.QuasiIsoTo P a K) :
    forgetBoundHom (𝟙 R) = 𝟙 R.forgetBound := sorry

/-- Forgetting a composite fixed-bound morphism is composition of the forgotten maps. -/
@[simp]
theorem forgetBoundHom_comp {R S T : StrictlyGE.TermsIn.QuasiIsoTo P a K}
    (f : R ⟶ S) (g : S ⟶ T) :
    forgetBoundHom (f ≫ g) = forgetBoundHom f ≫ forgetBoundHom g := sorry

/-- Functorially forget the specified lower cutoff of fixed-bound right resolutions. -/
@[stacks 05T6 "functorial cutoff-forgetting for bounded-below resolutions"]
def forgetBoundFunctor (P : ObjectProperty A) (a : ℤ) (K : CochainComplex A ℤ) :
    StrictlyGE.TermsIn.QuasiIsoTo P a K ⥤ Plus.TermsIn.QuasiIsoTo P K where
  obj R := R.forgetBound
  map f := forgetBoundHom f
  map_id := forgetBoundHom_id
  map_comp := forgetBoundHom_comp

/-- The cutoff-forgetting functor acts on objects by `forgetBound`. -/
@[simp]
theorem forgetBoundFunctor_obj (P : ObjectProperty A) (a : ℤ)
    (K : CochainComplex A ℤ) (R : StrictlyGE.TermsIn.QuasiIsoTo P a K) :
    (forgetBoundFunctor P a K).obj R = R.forgetBound := sorry

/-- The cutoff-forgetting functor retains the underlying model map. -/
@[simp]
theorem forgetBoundFunctor_map_f (P : ObjectProperty A) (a : ℤ)
    (K : CochainComplex A ℤ) {R S : StrictlyGE.TermsIn.QuasiIsoTo P a K}
    (f : R ⟶ S) :
    ((forgetBoundFunctor P a K).map f).f =
      (StrictlyGE.TermsIn.forgetBound P a).map f.f := sorry

end CochainComplex.StrictlyGE.TermsIn.QuasiIsoTo



namespace CochainComplex.Plus.TermsIn.QuasiIsoTo

variable {A : Type u} [Category.{v} A] [HasZeroMorphisms A] [CategoryWithHomology A]
  {P : ObjectProperty A} {K : CochainComplex A ℤ}

/-- Refine a variable-bound right resolution by an explicitly supplied lower cutoff. -/
@[stacks 05T6 "refining a bounded-below resolution by a specified cutoff"]
def withBound (R : Plus.TermsIn.QuasiIsoTo P K) (a : ℤ)
    (h : R.complex.IsStrictlyGE a) : StrictlyGE.TermsIn.QuasiIsoTo P a K :=
  StrictlyGE.TermsIn.QuasiIsoTo.mk
    ⟨R.complex, ⟨h, R.term_mem⟩⟩ R.comparison R.hw

/-- Refining by a cutoff retains the underlying resolving complex. -/
@[simp]
theorem withBound_complex (R : Plus.TermsIn.QuasiIsoTo P K) (a : ℤ)
    (h : R.complex.IsStrictlyGE a) :
    (R.withBound a h : CochainComplex A ℤ) = R.complex := sorry

/-- Refining by a cutoff retains the comparison map. -/
@[simp]
theorem withBound_comparison (R : Plus.TermsIn.QuasiIsoTo P K) (a : ℤ)
    (h : R.complex.IsStrictlyGE a) :
    (R.withBound a h).comparison = R.comparison := sorry

/-- Forgetting an explicitly supplied cutoff recovers the variable-bound resolution. -/
@[simp]
theorem forgetBound_withBound (R : Plus.TermsIn.QuasiIsoTo P K) (a : ℤ)
    (h : R.complex.IsStrictlyGE a) :
    (R.withBound a h).forgetBound = R := sorry

end CochainComplex.Plus.TermsIn.QuasiIsoTo


