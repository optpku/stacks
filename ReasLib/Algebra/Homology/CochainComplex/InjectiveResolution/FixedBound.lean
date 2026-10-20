/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.Algebra.Homology.CochainComplex.InjectiveResolution.Definition
public import ReasLib.Algebra.Homology.CochainComplex.BoundedBelowReplacement.Resolution.ForgetBound
public import ReasLib.Algebra.Homology.CochainComplex.BoundedBelowReplacement.Resolution.Mono

/-!
# Fixed-Bound Models as Injective Resolutions

This file specializes canonical fixed-lower-bound termwise-injective right models to
cochain-complex injective resolutions.
-/

@[expose] public section

open CategoryTheory CategoryTheory.ObjectProperty

universe v u

namespace CochainComplex

variable {𝒜 : Type u} [Category.{v} 𝒜] [Abelian 𝒜]

namespace StrictlyGE.TermsIn.QuasiIsoTo

variable {a : ℤ} {K : CochainComplex 𝒜 ℤ}

/-- Specialize a canonical fixed-lower-bound termwise-injective right model to an injective
resolution. -/
@[stacks 013I "fixed-bound right model as an injective resolution"]
abbrev toInjectiveResolution
    (R : StrictlyGE.TermsIn.QuasiIsoTo (isInjective 𝒜) a K) : InjectiveResolution K :=
  R.forgetBound

/-- Specialization to an injective resolution retains the bundled injective model after
forgetting its chosen cutoff. -/
@[simp]
theorem toInjectiveResolution_model
    (R : StrictlyGE.TermsIn.QuasiIsoTo (isInjective 𝒜) a K) :
    R.toInjectiveResolution.model =
      (StrictlyGE.TermsIn.forgetBound (isInjective 𝒜) a).obj R.model := sorry

/-- Specialization to an injective resolution retains the resolving complex. -/
@[simp]
theorem toInjectiveResolution_complex
    (R : StrictlyGE.TermsIn.QuasiIsoTo (isInjective 𝒜) a K) :
    (R.toInjectiveResolution.complex : CochainComplex 𝒜 ℤ) = R.complex := sorry

/-- Specialization to an injective resolution retains the comparison. -/
@[simp]
theorem toInjectiveResolution_ι
    (R : StrictlyGE.TermsIn.QuasiIsoTo (isInjective 𝒜) a K) :
    R.toInjectiveResolution.ι = R.comparison := sorry

namespace toInjectiveResolution

/-- Forget the cutoff on a morphism of fixed-bound injective models. -/
abbrev hom {R S : StrictlyGE.TermsIn.QuasiIsoTo (isInjective 𝒜) a K}
    (f : R ⟶ S) : R.toInjectiveResolution ⟶ S.toInjectiveResolution :=
  StrictlyGE.TermsIn.QuasiIsoTo.forgetBoundHom f

/-- Functorially specialize fixed-bound injective models to injective resolutions. -/
@[stacks 013I "functorial specialization of fixed-bound injective resolutions"]
abbrev functor (a : ℤ) (K : CochainComplex 𝒜 ℤ) :
    StrictlyGE.TermsIn.QuasiIsoTo (isInjective 𝒜) a K ⥤
      InjectiveResolution K :=
  StrictlyGE.TermsIn.QuasiIsoTo.forgetBoundFunctor (isInjective 𝒜) a K

/-- The specialization functor forgets the cutoff on objects. -/
@[simp]
theorem functor_obj (a : ℤ) (K : CochainComplex 𝒜 ℤ)
    (R : StrictlyGE.TermsIn.QuasiIsoTo (isInjective 𝒜) a K) :
    (functor a K).obj R = R.toInjectiveResolution := sorry

/-- The specialization functor forgets the cutoff on morphisms. -/
@[simp]
theorem functor_map (a : ℤ) (K : CochainComplex 𝒜 ℤ)
    {R S : StrictlyGE.TermsIn.QuasiIsoTo (isInjective 𝒜) a K}
    (f : R ⟶ S) :
    (functor a K).map f = hom f := sorry

/-- Specialization of a fixed-bound morphism retains its underlying cochain map. -/
@[simp]
theorem hom_hom {R S : StrictlyGE.TermsIn.QuasiIsoTo (isInjective 𝒜) a K}
    (f : R ⟶ S) :
    InjectiveResolution.hom (hom f) = StrictlyGE.TermsIn.QuasiIsoTo.hom f := sorry

end toInjectiveResolution

end StrictlyGE.TermsIn.QuasiIsoTo

namespace StrictlyGE.TermsIn.QuasiIsoTo.Mono

variable {a : ℤ} {K : CochainComplex 𝒜 ℤ}

/-- Specialize a canonical monomorphic fixed-lower-bound termwise-injective right model to an
injective resolution. -/
@[stacks 013I "monomorphic fixed-bound right model as an injective resolution"]
def toInjectiveResolution
    (R : StrictlyGE.TermsIn.QuasiIsoTo.Mono (isInjective 𝒜) a K) :
    InjectiveResolution K :=
  R.toQuasiIsoTo.toInjectiveResolution

/-- Strong specialization retains the bundled injective model after forgetting the monomorphism
condition and chosen cutoff. -/
@[simp]
theorem toInjectiveResolution_model
    (R : StrictlyGE.TermsIn.QuasiIsoTo.Mono (isInjective 𝒜) a K) :
    R.toInjectiveResolution.model =
      (StrictlyGE.TermsIn.forgetBound (isInjective 𝒜) a).obj R.model := sorry

/-- Strong specialization to an injective resolution retains the resolving complex. -/
@[simp]
theorem toInjectiveResolution_complex
    (R : StrictlyGE.TermsIn.QuasiIsoTo.Mono (isInjective 𝒜) a K) :
    (R.toInjectiveResolution.complex : CochainComplex 𝒜 ℤ) = R.complex := sorry

/-- Strong specialization to an injective resolution retains the comparison. -/
@[simp]
theorem toInjectiveResolution_ι
    (R : StrictlyGE.TermsIn.QuasiIsoTo.Mono (isInjective 𝒜) a K) :
    R.toInjectiveResolution.ι = R.comparison := sorry

namespace toInjectiveResolution

/-- Forget the monomorphism condition and cutoff on a morphism of strong fixed-bound injective
models. -/
abbrev hom
    {R S : StrictlyGE.TermsIn.QuasiIsoTo.Mono (isInjective 𝒜) a K}
    (f : R ⟶ S) : R.toInjectiveResolution ⟶ S.toInjectiveResolution :=
  StrictlyGE.TermsIn.QuasiIsoTo.toInjectiveResolution.hom
    (StrictlyGE.TermsIn.QuasiIsoTo.Mono.toQuasiIsoTo.hom f)

/-- Functorially specialize strong fixed-bound injective models to injective resolutions. -/
@[stacks 013I "functorial specialization of monomorphic injective resolutions"]
abbrev functor (a : ℤ) (K : CochainComplex 𝒜 ℤ) :
    StrictlyGE.TermsIn.QuasiIsoTo.Mono (isInjective 𝒜) a K ⥤
      InjectiveResolution K :=
  StrictlyGE.TermsIn.QuasiIsoTo.Mono.toQuasiIsoTo.functor
      (isInjective 𝒜) a K ⋙
    StrictlyGE.TermsIn.QuasiIsoTo.toInjectiveResolution.functor a K

/-- Strong specialization forgets the extra conditions on objects. -/
@[simp]
theorem functor_obj (a : ℤ) (K : CochainComplex 𝒜 ℤ)
    (R : StrictlyGE.TermsIn.QuasiIsoTo.Mono (isInjective 𝒜) a K) :
    (functor a K).obj R = R.toInjectiveResolution := sorry

/-- Strong specialization forgets the extra conditions on morphisms. -/
@[simp]
theorem functor_map (a : ℤ) (K : CochainComplex 𝒜 ℤ)
    {R S : StrictlyGE.TermsIn.QuasiIsoTo.Mono (isInjective 𝒜) a K}
    (f : R ⟶ S) :
    (functor a K).map f = hom f := sorry

/-- Strong specialization retains the underlying cochain map. -/
@[simp]
theorem hom_hom
    {R S : StrictlyGE.TermsIn.QuasiIsoTo.Mono (isInjective 𝒜) a K}
    (f : R ⟶ S) :
    InjectiveResolution.hom (hom f) =
      StrictlyGE.TermsIn.QuasiIsoTo.Mono.hom f := sorry

end toInjectiveResolution

end StrictlyGE.TermsIn.QuasiIsoTo.Mono

end CochainComplex


