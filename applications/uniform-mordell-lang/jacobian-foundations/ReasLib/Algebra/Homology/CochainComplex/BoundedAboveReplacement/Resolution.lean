module

public import ReasLib.Algebra.Homology.CochainComplex.Bounded.Fixed.Termwise
public import ReasLib.CategoryTheory.ObjectProperty.Localization.Resolution.Left
public import Mathlib.Algebra.Homology.QuasiIso
public import Mathlib.Tactic.CrossRefAttribute

/-!
# Quasi-Isomorphic Models with a Fixed Upper Bound

This file specializes Mathlib's left-resolution object to complexes that are strictly bounded
above at a fixed degree and whose terms satisfy a chosen object property.
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits

universe v u

namespace CochainComplex.StrictlyLE.TermsIn

variable {A : Type u} [Category.{v} A] [HasZeroMorphisms A] [CategoryWithHomology A]

/-- The fixed-upper-bound termwise inclusion as a morphism of quasi-isomorphism localizers. -/
abbrev localizer (P : ObjectProperty A) (a : ℤ) :=
  fullSubcategoryLocalizerMorphism (CochainComplex.StrictlyLE.termsIn P a)
    (HomologicalComplex.quasiIso A (ComplexShape.up ℤ))

/-- A quasi-isomorphism from a complex strictly bounded above at `a` with terms in `P` to `K`.
The underlying owner is Mathlib's left-resolution object. -/
@[stacks 05T7 "fixed-upper-bound property-indexed resolution"]
abbrev QuasiIsoFrom (P : ObjectProperty A) (a : ℤ) (K : CochainComplex A ℤ) :=
  ObjectProperty.LeftResolution (CochainComplex.StrictlyLE.termsIn P a)
    (HomologicalComplex.quasiIso A (ComplexShape.up ℤ)) K

namespace QuasiIsoFrom

variable {P : ObjectProperty A} {a : ℤ} {K : CochainComplex A ℤ}

/-- Construct a fixed-upper-bound termwise left model from explicit comparison data. -/
def mk (M : CochainComplex.StrictlyLE.TermsIn P a) (f : M.obj ⟶ K) (hf : QuasiIso f) :
    QuasiIsoFrom P a K where
  X₁ := M
  w := f
  hw := hf

/-- The bundled fixed-upper-bound termwise model. -/
abbrev model (R : QuasiIsoFrom P a K) : CochainComplex.StrictlyLE.TermsIn P a :=
  R.X₁

/-- The cochain complex underlying a fixed-upper-bound left model. -/
abbrev complex (R : QuasiIsoFrom P a K) : CochainComplex A ℤ :=
  R.model.obj

/-- The quasi-isomorphic comparison from the left model to the original complex. -/
abbrev comparison (R : QuasiIsoFrom P a K) : R.complex ⟶ K :=
  R.w

/-- Conventional name for the comparison from a fixed-upper-bound left model. -/
abbrev π (R : QuasiIsoFrom P a K) : R.complex ⟶ K :=
  R.comparison

/-- A fixed-upper-bound left model coerces to its underlying cochain complex. -/
instance : CoeOut (QuasiIsoFrom P a K) (CochainComplex A ℤ) where
  coe R := R.complex

/-- The model retains the specified strict upper bound. -/
instance complex_isStrictlyLE (R : QuasiIsoFrom P a K) : R.complex.IsStrictlyLE a := sorry

/-- Every term of the model satisfies the chosen object property. -/
theorem term_mem (R : QuasiIsoFrom P a K) (i : ℤ) : P (R.complex.X i) := sorry

/-- The comparison from the model is a quasi-isomorphism. -/
instance comparison_quasiIso (R : QuasiIsoFrom P a K) : QuasiIso R.comparison := sorry

/-- The bundled model map underlying a morphism of fixed-bound left resolutions. -/
abbrev modelHom {R S : QuasiIsoFrom P a K} (f : R ⟶ S) : R.model ⟶ S.model :=
  ObjectProperty.LeftResolution.modelHom f

/-- Morphisms of fixed-upper-bound left resolutions are determined by their bundled model
morphisms. -/
@[ext]
theorem hom_ext {R S : QuasiIsoFrom P a K} {f g : R ⟶ S}
    (h : modelHom f = modelHom g) : f = g := sorry

/-- The cochain map underlying a morphism of fixed-bound left resolutions. -/
abbrev hom {R S : QuasiIsoFrom P a K} (f : R ⟶ S) : R.complex ⟶ S.complex :=
  ObjectProperty.LeftResolution.hom f

/-- The cochain map of a fixed-bound morphism is obtained by forgetting its bundled model
morphism. -/
@[simp]
theorem hom_eq_map_modelHom {R S : QuasiIsoFrom P a K} (f : R ⟶ S) :
    hom f = (StrictlyLE.TermsIn.ι P a).map (modelHom f) := sorry

/-- The identity fixed-bound morphism has identity bundled model morphism. -/
@[simp]
theorem id_modelHom (R : QuasiIsoFrom P a K) : modelHom (𝟙 R) = 𝟙 R.model := sorry

/-- Bundled model morphisms preserve composition of fixed-bound left-resolution morphisms. -/
@[simp]
theorem comp_modelHom {R S T : QuasiIsoFrom P a K} (f : R ⟶ S) (g : S ⟶ T) :
    modelHom (f ≫ g) = modelHom f ≫ modelHom g := sorry

/-- The identity resolution morphism induces the identity cochain map. -/
@[simp]
theorem id_hom (R : QuasiIsoFrom P a K) : hom (𝟙 R) = 𝟙 R.complex := sorry

/-- Composition of resolution morphisms induces composition of cochain maps. -/
@[simp]
theorem comp_hom {R S T : QuasiIsoFrom P a K} (f : R ⟶ S) (g : S ⟶ T) :
    hom (f ≫ g) = hom f ≫ hom g := sorry

/-- A morphism of fixed-bound left resolutions commutes with the comparisons. -/
@[reassoc]
theorem comparison_naturality {R S : QuasiIsoFrom P a K} (f : R ⟶ S) :
    hom f ≫ S.comparison = R.comparison := sorry

/-- The functor selecting the bundled fixed-upper-bound model. -/
abbrev modelFunctor (P : ObjectProperty A) (a : ℤ) (K : CochainComplex A ℤ) :
    QuasiIsoFrom P a K ⥤ StrictlyLE.TermsIn P a :=
  LocalizerMorphism.LeftResolution.modelFunctor (localizer P a) K

/-- The fixed-bound model functor returns the bundled model. -/
@[simp]
theorem modelFunctor_obj (R : QuasiIsoFrom P a K) :
    (modelFunctor P a K).obj R = R.model := sorry

/-- The fixed-bound model functor retains the bundled model map. -/
@[simp]
theorem modelFunctor_map {R S : QuasiIsoFrom P a K} (f : R ⟶ S) :
    (modelFunctor P a K).map f = modelHom f := sorry

/-- The functor selecting the underlying cochain complex of a fixed-bound left resolution. -/
abbrev complexFunctor (P : ObjectProperty A) (a : ℤ) (K : CochainComplex A ℤ) :
    QuasiIsoFrom P a K ⥤ CochainComplex A ℤ :=
  LocalizerMorphism.LeftResolution.objectFunctor (localizer P a) K

/-- The underlying-complex functor returns the resolving complex. -/
@[simp]
theorem complexFunctor_obj (R : QuasiIsoFrom P a K) :
    (complexFunctor P a K).obj R = R.complex := sorry

/-- The underlying-complex functor retains the cochain map. -/
@[simp]
theorem complexFunctor_map {R S : QuasiIsoFrom P a K} (f : R ⟶ S) :
    (complexFunctor P a K).map f = hom f := sorry

/-- Forgetting the bundled fixed-bound models identifies the model and complex functors. -/
theorem modelFunctor_comp_ι (P : ObjectProperty A) (a : ℤ) (K : CochainComplex A ℤ) :
    modelFunctor P a K ⋙ StrictlyLE.TermsIn.ι P a = complexFunctor P a K := sorry

/-- The fixed-bound comparisons form a natural transformation. -/
abbrev comparisonNatTrans (P : ObjectProperty A) (a : ℤ) (K : CochainComplex A ℤ) :
    complexFunctor P a K ⟶ (Functor.const (QuasiIsoFrom P a K)).obj K :=
  LocalizerMorphism.LeftResolution.comparisonNatTrans (localizer P a) K

/-- Evaluating the comparison transformation gives the resolution comparison. -/
@[simp]
theorem comparisonNatTrans_app (R : QuasiIsoFrom P a K) :
    (comparisonNatTrans P a K).app R = R.comparison := sorry

/-- Fixed-upper-bound left models are nonempty exactly when explicit model data exist. -/
theorem nonempty_iff :
    Nonempty (QuasiIsoFrom P a K) ↔
      ∃ (M : CochainComplex.StrictlyLE.TermsIn P a) (f : M.obj ⟶ K), QuasiIso f := sorry

/-- The model selected by `mk` is the supplied fixed-upper-bound complex. -/
@[simp]
theorem mk_model (M : CochainComplex.StrictlyLE.TermsIn P a) (f : M.obj ⟶ K)
    (hf : QuasiIso f) :
    (mk M f hf).model = M := sorry

/-- The comparison selected by `mk` is the supplied quasi-isomorphism. -/
@[simp]
theorem mk_comparison (M : CochainComplex.StrictlyLE.TermsIn P a) (f : M.obj ⟶ K)
    (hf : QuasiIso f) :
    (mk M f hf).comparison = f := sorry

end QuasiIsoFrom

end CochainComplex.StrictlyLE.TermsIn


