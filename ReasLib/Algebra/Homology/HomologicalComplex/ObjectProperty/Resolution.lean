module

public import ReasLib.Algebra.Homology.HomologicalComplex.ObjectProperty
public import ReasLib.CategoryTheory.ObjectProperty.Localization.Resolution
public import Mathlib.Algebra.Homology.QuasiIso
public import Mathlib.Tactic.CrossRefAttribute

/-!
# Termwise Quasi-Isomorphic Models of Homological Complexes

This file combines the termwise object property on homological complexes with Mathlib's
`LocalizerMorphism.RightResolution` and `LocalizerMorphism.LeftResolution`.  Thus a
property-indexed quasi-isomorphic model inherits the standard resolution category and map API
instead of introducing a parallel witness structure.
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits

universe v u w

namespace HomologicalComplex.TermsIn

variable {C : Type u} [Category.{v} C] [HasZeroMorphisms C] [CategoryWithHomology C]
variable {I : Type w} (c : ComplexShape I)

/-- The inclusion of termwise-`P` homological complexes, regarded as a morphism of the
quasi-isomorphism localizers. -/
abbrev localizer (P : ObjectProperty C) :=
  fullSubcategoryLocalizerMorphism (HomologicalComplex.termsIn c P)
    (HomologicalComplex.quasiIso C c)

/-- A quasi-isomorphic model of `K` whose terms satisfy `P`, with comparison directed from
`K` to the model.  This is Mathlib's right-resolution object for the termwise-`P` inclusion. -/
@[stacks 013I "property-indexed quasi-isomorphic right model"]
abbrev QuasiIsoTo (P : ObjectProperty C) (K : HomologicalComplex C c) :=
  ObjectProperty.RightResolution (HomologicalComplex.termsIn c P)
    (HomologicalComplex.quasiIso C c) K

/-- A quasi-isomorphic model of `K` whose terms satisfy `P`, with comparison directed from
the model to `K`.  This is Mathlib's left-resolution object for the termwise-`P` inclusion. -/
@[stacks 0643 "property-indexed quasi-isomorphic left model"]
abbrev QuasiIsoFrom (P : ObjectProperty C) (K : HomologicalComplex C c) :=
  ObjectProperty.LeftResolution (HomologicalComplex.termsIn c P)
    (HomologicalComplex.quasiIso C c) K

namespace QuasiIsoTo

variable {c : ComplexShape I} {P : ObjectProperty C} {K : HomologicalComplex C c}

/-- Construct a termwise-`P` right model from explicit comparison data. -/
def mk (M : HomologicalComplex.TermsIn c P) (f : K ⟶ M.obj) (hf : QuasiIso f) :
    QuasiIsoTo c P K where
  X₁ := M
  w := f
  hw := hf

/-- The bundled termwise-`P` model underlying a right model. -/
abbrev model (R : QuasiIsoTo c P K) : HomologicalComplex.TermsIn c P :=
  R.X₁

/-- The homological complex underlying a termwise-`P` right model. -/
abbrev complex (R : QuasiIsoTo c P K) : HomologicalComplex C c :=
  R.model.obj

/-- The quasi-isomorphic comparison from the original complex to a right model. -/
abbrev comparison (R : QuasiIsoTo c P K) : K ⟶ R.complex :=
  R.w

/-- A right model coerces to its underlying homological complex. -/
instance : CoeOut (QuasiIsoTo c P K) (HomologicalComplex C c) where
  coe R := R.complex

/-- Every term of a property-indexed right model satisfies the chosen object property. -/
theorem term_mem (R : QuasiIsoTo c P K) (i : I) : P (R.complex.X i) := sorry

/-- The comparison of a property-indexed right model is a quasi-isomorphism. -/
instance comparison_quasiIso (R : QuasiIsoTo c P K) : QuasiIso R.comparison := sorry

/-- Right models are nonempty exactly when an explicit termwise-`P` target and
quasi-isomorphism to it exist. -/
theorem nonempty_iff :
    Nonempty (QuasiIsoTo c P K) ↔
      ∃ (M : HomologicalComplex.TermsIn c P) (f : K ⟶ M.obj), QuasiIso f := sorry

/-- The model selected by `mk` is the supplied termwise-`P` complex. -/
@[simp]
theorem mk_model (M : HomologicalComplex.TermsIn c P) (f : K ⟶ M.obj) (hf : QuasiIso f) :
    (mk M f hf).model = M := sorry

/-- The comparison selected by `mk` is the supplied quasi-isomorphism. -/
@[simp]
theorem mk_comparison (M : HomologicalComplex.TermsIn c P) (f : K ⟶ M.obj)
    (hf : QuasiIso f) :
    (mk M f hf).comparison = f := sorry

end QuasiIsoTo

namespace QuasiIsoFrom

variable {c : ComplexShape I} {P : ObjectProperty C} {K : HomologicalComplex C c}

/-- Construct a termwise-`P` left model from explicit comparison data. -/
def mk (M : HomologicalComplex.TermsIn c P) (f : M.obj ⟶ K) (hf : QuasiIso f) :
    QuasiIsoFrom c P K where
  X₁ := M
  w := f
  hw := hf

/-- The bundled termwise-`P` model underlying a left model. -/
abbrev model (R : QuasiIsoFrom c P K) : HomologicalComplex.TermsIn c P :=
  R.X₁

/-- The homological complex underlying a termwise-`P` left model. -/
abbrev complex (R : QuasiIsoFrom c P K) : HomologicalComplex C c :=
  R.model.obj

/-- The quasi-isomorphic comparison from a left model to the original complex. -/
abbrev comparison (R : QuasiIsoFrom c P K) : R.complex ⟶ K :=
  R.w

/-- A left model coerces to its underlying homological complex. -/
instance : CoeOut (QuasiIsoFrom c P K) (HomologicalComplex C c) where
  coe R := R.complex

/-- Every term of a property-indexed left model satisfies the chosen object property. -/
theorem term_mem (R : QuasiIsoFrom c P K) (i : I) : P (R.complex.X i) := sorry

/-- The comparison of a property-indexed left model is a quasi-isomorphism. -/
instance comparison_quasiIso (R : QuasiIsoFrom c P K) : QuasiIso R.comparison := sorry

/-- Left models are nonempty exactly when an explicit termwise-`P` source and
quasi-isomorphism from it exist. -/
theorem nonempty_iff :
    Nonempty (QuasiIsoFrom c P K) ↔
      ∃ (M : HomologicalComplex.TermsIn c P) (f : M.obj ⟶ K), QuasiIso f := sorry

/-- The model selected by `mk` is the supplied termwise-`P` complex. -/
@[simp]
theorem mk_model (M : HomologicalComplex.TermsIn c P) (f : M.obj ⟶ K) (hf : QuasiIso f) :
    (mk M f hf).model = M := sorry

/-- The comparison selected by `mk` is the supplied quasi-isomorphism. -/
@[simp]
theorem mk_comparison (M : HomologicalComplex.TermsIn c P) (f : M.obj ⟶ K)
    (hf : QuasiIso f) :
    (mk M f hf).comparison = f := sorry

end QuasiIsoFrom

end HomologicalComplex.TermsIn
