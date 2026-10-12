/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import ReasLib.Algebra.Homology.CochainComplex.Bounded.Fixed.Termwise
public import ReasLib.CategoryTheory.ObjectProperty.Localization.Resolution.Right
public import Mathlib.Algebra.Homology.QuasiIso
public import Mathlib.Tactic.CrossRefAttribute

/-!
# Quasi-Isomorphic Models with a Fixed Lower Bound

This file specializes Mathlib's right-resolution object to complexes that are strictly bounded
below at a fixed degree and whose terms satisfy a chosen object property.
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits

universe v u

namespace CochainComplex.StrictlyGE.TermsIn

variable {A : Type u} [Category.{v} A] [HasZeroMorphisms A] [CategoryWithHomology A]

/-- The fixed-lower-bound termwise inclusion as a morphism of quasi-isomorphism localizers. -/
abbrev localizer (P : ObjectProperty A) (a : ℤ) :=
  fullSubcategoryLocalizerMorphism (CochainComplex.StrictlyGE.termsIn P a)
    (HomologicalComplex.quasiIso A (ComplexShape.up ℤ))

/-- A quasi-isomorphism from `K` to a complex strictly bounded below at `a` with terms in `P`.
The underlying owner is Mathlib's right-resolution object. -/
@[stacks 05T6 "fixed-lower-bound property-indexed resolution"]
abbrev QuasiIsoTo (P : ObjectProperty A) (a : ℤ) (K : CochainComplex A ℤ) :=
  ObjectProperty.RightResolution (CochainComplex.StrictlyGE.termsIn P a)
    (HomologicalComplex.quasiIso A (ComplexShape.up ℤ)) K

namespace QuasiIsoTo

variable {P : ObjectProperty A} {a : ℤ} {K : CochainComplex A ℤ}

/-- Construct a fixed-lower-bound termwise right model from explicit comparison data. -/
def mk (M : CochainComplex.StrictlyGE.TermsIn P a) (f : K ⟶ M.obj) (hf : QuasiIso f) :
    QuasiIsoTo P a K where
  X₁ := M
  w := f
  hw := hf

/-- The bundled fixed-lower-bound termwise model. -/
abbrev model (R : QuasiIsoTo P a K) : CochainComplex.StrictlyGE.TermsIn P a :=
  R.X₁

/-- The cochain complex underlying a fixed-lower-bound right model. -/
abbrev complex (R : QuasiIsoTo P a K) : CochainComplex A ℤ :=
  R.model.obj

/-- The quasi-isomorphic comparison from the original complex to the right model. -/
abbrev comparison (R : QuasiIsoTo P a K) : K ⟶ R.complex :=
  R.w

/-- Conventional name for the comparison into a fixed-lower-bound right model. -/
abbrev ι (R : QuasiIsoTo P a K) : K ⟶ R.complex :=
  R.comparison

/-- A fixed-lower-bound right model coerces to its underlying cochain complex. -/
instance : CoeOut (QuasiIsoTo P a K) (CochainComplex A ℤ) where
  coe R := R.complex

/-- The model retains the specified strict lower bound. -/
instance complex_isStrictlyGE (R : QuasiIsoTo P a K) : R.complex.IsStrictlyGE a := sorry

/-- Every term of the model satisfies the chosen object property. -/
theorem term_mem (R : QuasiIsoTo P a K) (i : ℤ) : P (R.complex.X i) := sorry

/-- The comparison into the model is a quasi-isomorphism. -/
instance comparison_quasiIso (R : QuasiIsoTo P a K) : QuasiIso R.comparison := sorry

/-- The bundled model map underlying a morphism of fixed-bound right resolutions. -/
abbrev modelHom {R S : QuasiIsoTo P a K} (f : R ⟶ S) : R.model ⟶ S.model :=
  ObjectProperty.RightResolution.modelHom f

/-- Morphisms of fixed-lower-bound right resolutions are determined by their bundled model
morphisms. -/
@[ext]
theorem hom_ext {R S : QuasiIsoTo P a K} {f g : R ⟶ S}
    (h : modelHom f = modelHom g) : f = g := sorry

/-- The cochain map underlying a morphism of fixed-bound right resolutions. -/
abbrev hom {R S : QuasiIsoTo P a K} (f : R ⟶ S) : R.complex ⟶ S.complex :=
  ObjectProperty.RightResolution.hom f

/-- The cochain map of a fixed-bound morphism is obtained by forgetting its bundled model
morphism. -/
@[simp]
theorem hom_eq_map_modelHom {R S : QuasiIsoTo P a K} (f : R ⟶ S) :
    hom f = (StrictlyGE.TermsIn.ι P a).map (modelHom f) := sorry

/-- The identity fixed-bound morphism has identity bundled model morphism. -/
@[simp]
theorem id_modelHom (R : QuasiIsoTo P a K) : modelHom (𝟙 R) = 𝟙 R.model := sorry

/-- Bundled model morphisms preserve composition of fixed-bound right-resolution morphisms. -/
@[simp]
theorem comp_modelHom {R S T : QuasiIsoTo P a K} (f : R ⟶ S) (g : S ⟶ T) :
    modelHom (f ≫ g) = modelHom f ≫ modelHom g := sorry

/-- The identity resolution morphism induces the identity cochain map. -/
@[simp]
theorem id_hom (R : QuasiIsoTo P a K) : hom (𝟙 R) = 𝟙 R.complex := sorry

/-- Composition of resolution morphisms induces composition of cochain maps. -/
@[simp]
theorem comp_hom {R S T : QuasiIsoTo P a K} (f : R ⟶ S) (g : S ⟶ T) :
    hom (f ≫ g) = hom f ≫ hom g := sorry

/-- A morphism of fixed-bound right resolutions commutes with the comparisons. -/
@[reassoc]
theorem comparison_naturality {R S : QuasiIsoTo P a K} (f : R ⟶ S) :
    R.comparison ≫ hom f = S.comparison := sorry

/-- The functor selecting the bundled fixed-lower-bound model. -/
abbrev modelFunctor (P : ObjectProperty A) (a : ℤ) (K : CochainComplex A ℤ) :
    QuasiIsoTo P a K ⥤ StrictlyGE.TermsIn P a :=
  LocalizerMorphism.RightResolution.modelFunctor (localizer P a) K

/-- The fixed-bound model functor returns the bundled model. -/
@[simp]
theorem modelFunctor_obj (R : QuasiIsoTo P a K) :
    (modelFunctor P a K).obj R = R.model := sorry

/-- The fixed-bound model functor retains the bundled model map. -/
@[simp]
theorem modelFunctor_map {R S : QuasiIsoTo P a K} (f : R ⟶ S) :
    (modelFunctor P a K).map f = modelHom f := sorry

/-- The functor selecting the underlying cochain complex of a fixed-bound right resolution. -/
abbrev complexFunctor (P : ObjectProperty A) (a : ℤ) (K : CochainComplex A ℤ) :
    QuasiIsoTo P a K ⥤ CochainComplex A ℤ :=
  LocalizerMorphism.RightResolution.objectFunctor (localizer P a) K

/-- The underlying-complex functor returns the resolving complex. -/
@[simp]
theorem complexFunctor_obj (R : QuasiIsoTo P a K) :
    (complexFunctor P a K).obj R = R.complex := sorry

/-- The underlying-complex functor retains the cochain map. -/
@[simp]
theorem complexFunctor_map {R S : QuasiIsoTo P a K} (f : R ⟶ S) :
    (complexFunctor P a K).map f = hom f := sorry

/-- Forgetting the bundled fixed-bound models identifies the model and complex functors. -/
theorem modelFunctor_comp_ι (P : ObjectProperty A) (a : ℤ) (K : CochainComplex A ℤ) :
    modelFunctor P a K ⋙ StrictlyGE.TermsIn.ι P a = complexFunctor P a K := sorry

/-- The fixed-bound comparisons form a natural transformation. -/
abbrev comparisonNatTrans (P : ObjectProperty A) (a : ℤ) (K : CochainComplex A ℤ) :
    (Functor.const (QuasiIsoTo P a K)).obj K ⟶ complexFunctor P a K :=
  LocalizerMorphism.RightResolution.comparisonNatTrans (localizer P a) K

/-- Evaluating the comparison transformation gives the resolution comparison. -/
@[simp]
theorem comparisonNatTrans_app (R : QuasiIsoTo P a K) :
    (comparisonNatTrans P a K).app R = R.comparison := sorry

/-- Fixed-lower-bound right models are nonempty exactly when explicit model data exist. -/
theorem nonempty_iff :
    Nonempty (QuasiIsoTo P a K) ↔
      ∃ (M : CochainComplex.StrictlyGE.TermsIn P a) (f : K ⟶ M.obj), QuasiIso f := sorry

/-- The model selected by `mk` is the supplied fixed-lower-bound complex. -/
@[simp]
theorem mk_model (M : CochainComplex.StrictlyGE.TermsIn P a) (f : K ⟶ M.obj)
    (hf : QuasiIso f) :
    (mk M f hf).model = M := sorry

/-- The comparison selected by `mk` is the supplied quasi-isomorphism. -/
@[simp]
theorem mk_comparison (M : CochainComplex.StrictlyGE.TermsIn P a) (f : K ⟶ M.obj)
    (hf : QuasiIso f) :
    (mk M f hf).comparison = f := sorry

end QuasiIsoTo

end CochainComplex.StrictlyGE.TermsIn


