/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import ReasLib.Algebra.Homology.CochainComplex.ProjectiveResolution.Basic
public import ReasLib.Algebra.Homology.CochainComplex.BoundedAboveReplacement.Resolution.ForgetBound
public import ReasLib.Algebra.Homology.CochainComplex.BoundedAboveReplacement.Resolution.Epi

/-!
# Fixed-Bound Models as Projective Resolutions

This file specializes canonical fixed-upper-bound termwise-projective left models to
cochain-complex projective resolutions.
-/

@[expose] public section

open CategoryTheory CategoryTheory.ObjectProperty

universe v u

namespace CochainComplex

variable {𝒜 : Type u} [Category.{v} 𝒜] [Abelian 𝒜]

namespace StrictlyLE.TermsIn.QuasiIsoFrom

variable {a : ℤ} {K : CochainComplex 𝒜 ℤ}

/-- Specialize a canonical fixed-upper-bound termwise-projective left model to a projective
resolution. -/
@[stacks 0643 "fixed-bound left model as a projective resolution"]
abbrev toProjectiveResolution
    (R : StrictlyLE.TermsIn.QuasiIsoFrom (isProjective 𝒜) a K) :
    ProjectiveResolution K :=
  R.forgetBound

/-- Specialization to a projective resolution retains the bundled projective model after
forgetting its chosen cutoff. -/
@[simp]
theorem toProjectiveResolution_model
    (R : StrictlyLE.TermsIn.QuasiIsoFrom (isProjective 𝒜) a K) :
    R.toProjectiveResolution.model =
      (StrictlyLE.TermsIn.forgetBound (isProjective 𝒜) a).obj R.model := sorry

/-- Specialization to a projective resolution retains the resolving complex. -/
@[simp]
theorem toProjectiveResolution_complex
    (R : StrictlyLE.TermsIn.QuasiIsoFrom (isProjective 𝒜) a K) :
    (R.toProjectiveResolution.complex : CochainComplex 𝒜 ℤ) = R.complex := sorry

/-- Specialization to a projective resolution retains the comparison. -/
@[simp]
theorem toProjectiveResolution_π
    (R : StrictlyLE.TermsIn.QuasiIsoFrom (isProjective 𝒜) a K) :
    R.toProjectiveResolution.π = R.comparison := sorry

namespace toProjectiveResolution

/-- Forget the cutoff on a morphism of fixed-bound projective models. -/
abbrev hom {R S : StrictlyLE.TermsIn.QuasiIsoFrom (isProjective 𝒜) a K}
    (f : R ⟶ S) : R.toProjectiveResolution ⟶ S.toProjectiveResolution :=
  StrictlyLE.TermsIn.QuasiIsoFrom.forgetBoundHom f

/-- Functorially specialize fixed-bound projective models to projective resolutions. -/
@[stacks 0643 "functorial specialization of fixed-bound projective resolutions"]
abbrev functor (a : ℤ) (K : CochainComplex 𝒜 ℤ) :
    StrictlyLE.TermsIn.QuasiIsoFrom (isProjective 𝒜) a K ⥤
      ProjectiveResolution K :=
  StrictlyLE.TermsIn.QuasiIsoFrom.forgetBoundFunctor (isProjective 𝒜) a K

/-- The specialization functor forgets the cutoff on objects. -/
@[simp]
theorem functor_obj (a : ℤ) (K : CochainComplex 𝒜 ℤ)
    (R : StrictlyLE.TermsIn.QuasiIsoFrom (isProjective 𝒜) a K) :
    (functor a K).obj R = R.toProjectiveResolution := sorry

/-- The specialization functor forgets the cutoff on morphisms. -/
@[simp]
theorem functor_map (a : ℤ) (K : CochainComplex 𝒜 ℤ)
    {R S : StrictlyLE.TermsIn.QuasiIsoFrom (isProjective 𝒜) a K}
    (f : R ⟶ S) :
    (functor a K).map f = hom f := sorry

/-- Specialization of a fixed-bound morphism retains its underlying cochain map. -/
@[simp]
theorem hom_hom {R S : StrictlyLE.TermsIn.QuasiIsoFrom (isProjective 𝒜) a K}
    (f : R ⟶ S) :
    ProjectiveResolution.hom (hom f) = StrictlyLE.TermsIn.QuasiIsoFrom.hom f := sorry

end toProjectiveResolution

end StrictlyLE.TermsIn.QuasiIsoFrom

namespace StrictlyLE.TermsIn.QuasiIsoFrom.Epi

variable {a : ℤ} {K : CochainComplex 𝒜 ℤ}

/-- Specialize a canonical epimorphic fixed-upper-bound termwise-projective left model to a
projective resolution. -/
@[stacks 0643 "epimorphic fixed-bound left model as a projective resolution"]
def toProjectiveResolution
    (R : StrictlyLE.TermsIn.QuasiIsoFrom.Epi (isProjective 𝒜) a K) :
    ProjectiveResolution K :=
  R.toQuasiIsoFrom.toProjectiveResolution

/-- Strong specialization retains the bundled projective model after forgetting the epimorphism
condition and chosen cutoff. -/
@[simp]
theorem toProjectiveResolution_model
    (R : StrictlyLE.TermsIn.QuasiIsoFrom.Epi (isProjective 𝒜) a K) :
    R.toProjectiveResolution.model =
      (StrictlyLE.TermsIn.forgetBound (isProjective 𝒜) a).obj R.model := sorry

/-- Strong specialization to a projective resolution retains the resolving complex. -/
@[simp]
theorem toProjectiveResolution_complex
    (R : StrictlyLE.TermsIn.QuasiIsoFrom.Epi (isProjective 𝒜) a K) :
    (R.toProjectiveResolution.complex : CochainComplex 𝒜 ℤ) = R.complex := sorry

/-- Strong specialization to a projective resolution retains the comparison. -/
@[simp]
theorem toProjectiveResolution_π
    (R : StrictlyLE.TermsIn.QuasiIsoFrom.Epi (isProjective 𝒜) a K) :
    R.toProjectiveResolution.π = R.comparison := sorry

namespace toProjectiveResolution

/-- Forget the epimorphism condition and cutoff on a morphism of strong fixed-bound projective
models. -/
abbrev hom
    {R S : StrictlyLE.TermsIn.QuasiIsoFrom.Epi (isProjective 𝒜) a K}
    (f : R ⟶ S) : R.toProjectiveResolution ⟶ S.toProjectiveResolution :=
  StrictlyLE.TermsIn.QuasiIsoFrom.toProjectiveResolution.hom
    (StrictlyLE.TermsIn.QuasiIsoFrom.Epi.toQuasiIsoFrom.hom f)

/-- Functorially specialize strong fixed-bound projective models to projective resolutions. -/
@[stacks 0643 "functorial specialization of epimorphic projective resolutions"]
abbrev functor (a : ℤ) (K : CochainComplex 𝒜 ℤ) :
    StrictlyLE.TermsIn.QuasiIsoFrom.Epi (isProjective 𝒜) a K ⥤
      ProjectiveResolution K :=
  StrictlyLE.TermsIn.QuasiIsoFrom.Epi.toQuasiIsoFrom.functor
      (isProjective 𝒜) a K ⋙
    StrictlyLE.TermsIn.QuasiIsoFrom.toProjectiveResolution.functor a K

/-- Strong specialization forgets the extra conditions on objects. -/
@[simp]
theorem functor_obj (a : ℤ) (K : CochainComplex 𝒜 ℤ)
    (R : StrictlyLE.TermsIn.QuasiIsoFrom.Epi (isProjective 𝒜) a K) :
    (functor a K).obj R = R.toProjectiveResolution := sorry

/-- Strong specialization forgets the extra conditions on morphisms. -/
@[simp]
theorem functor_map (a : ℤ) (K : CochainComplex 𝒜 ℤ)
    {R S : StrictlyLE.TermsIn.QuasiIsoFrom.Epi (isProjective 𝒜) a K}
    (f : R ⟶ S) :
    (functor a K).map f = hom f := sorry

/-- Strong specialization retains the underlying cochain map. -/
@[simp]
theorem hom_hom
    {R S : StrictlyLE.TermsIn.QuasiIsoFrom.Epi (isProjective 𝒜) a K}
    (f : R ⟶ S) :
    ProjectiveResolution.hom (hom f) =
      StrictlyLE.TermsIn.QuasiIsoFrom.Epi.hom f := sorry

end toProjectiveResolution

end StrictlyLE.TermsIn.QuasiIsoFrom.Epi

end CochainComplex
