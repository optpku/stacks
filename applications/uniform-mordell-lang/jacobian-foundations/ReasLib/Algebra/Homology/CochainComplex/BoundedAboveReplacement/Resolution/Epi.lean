module

public import ReasLib.Algebra.Homology.CochainComplex.BoundedAboveReplacement.Resolution
public import ReasLib.Algebra.Homology.HomologicalComplex.MonoEpi
public import ReasLib.Algebra.Homology.HomologicalComplex.QuasiIso.MonoEpi
public import ReasLib.CategoryTheory.ObjectProperty.Localization.Resolution.Left.Monotonicity
public import Mathlib.Tactic.CrossRefAttribute

/-!
# Epimorphic Quasi-Isomorphic Models with a Fixed Upper Bound

This file refines fixed-upper-bound left models by requiring the comparison to be an
epimorphism in the category of complexes.  Degreewise epimorphisms are exposed as a derived API
when the ambient category has pushouts.
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits

universe v u

namespace CochainComplex.StrictlyLE.TermsIn.QuasiIsoFrom

variable {A : Type u} [Category.{v} A] [HasZeroMorphisms A] [CategoryWithHomology A]

/-- An epimorphic quasi-isomorphism from a complex strictly bounded above at `a` whose terms
satisfy `P` to `K`.  The denominator is the intersection of quasi-isomorphisms and categorical
epimorphisms. -/
@[stacks 05T7 "epimorphic fixed-upper-bound property-indexed resolution"]
abbrev Epi (P : ObjectProperty A) (a : ℤ) (K : CochainComplex A ℤ) :=
  ObjectProperty.LeftResolution (CochainComplex.StrictlyLE.termsIn P a)
    (HomologicalComplex.quasiIsoEpi A (ComplexShape.up ℤ)) K

namespace Epi

variable {P : ObjectProperty A} {a : ℤ} {K : CochainComplex A ℤ}

/-- Construct an epimorphic fixed-upper-bound model from explicit comparison data. -/
def mk (M : CochainComplex.StrictlyLE.TermsIn P a) (f : M.obj ⟶ K)
    (hf : QuasiIso f) (he : _root_.CategoryTheory.Epi f) : QuasiIsoFrom.Epi P a K :=
  ObjectProperty.LeftResolution.mk M f ⟨hf, he⟩

/-- The bundled fixed-upper-bound termwise model. -/
abbrev model (R : QuasiIsoFrom.Epi P a K) : CochainComplex.StrictlyLE.TermsIn P a :=
  ObjectProperty.LeftResolution.model R

/-- The cochain complex underlying an epimorphic left model. -/
abbrev complex (R : QuasiIsoFrom.Epi P a K) : CochainComplex A ℤ :=
  ObjectProperty.LeftResolution.object R

/-- The epimorphic quasi-isomorphism from the model to the original complex. -/
abbrev comparison (R : QuasiIsoFrom.Epi P a K) : R.complex ⟶ K :=
  ObjectProperty.LeftResolution.comparison R

/-- Conventional name for the comparison from an epimorphic left model. -/
abbrev π (R : QuasiIsoFrom.Epi P a K) : R.complex ⟶ K :=
  R.comparison

/-- An epimorphic fixed-upper-bound left model coerces to its underlying complex. -/
instance : CoeOut (QuasiIsoFrom.Epi P a K) (CochainComplex A ℤ) where
  coe R := R.complex

/-- The model retains the specified strict upper bound. -/
instance complex_isStrictlyLE (R : QuasiIsoFrom.Epi P a K) : R.complex.IsStrictlyLE a := sorry

/-- Every term of the model satisfies the chosen object property. -/
theorem term_mem (R : QuasiIsoFrom.Epi P a K) (i : ℤ) : P (R.complex.X i) := sorry

/-- The comparison from the model is a quasi-isomorphism. -/
instance comparison_quasiIso (R : QuasiIsoFrom.Epi P a K) : QuasiIso R.comparison := sorry

/-- The comparison from the model is an epimorphism of complexes. -/
instance comparison_epi (R : QuasiIsoFrom.Epi P a K) :
    _root_.CategoryTheory.Epi R.comparison := sorry

/-- With pushouts, every component of the comparison is epimorphic. -/
theorem comparison_epi_f [HasPushouts A] (R : QuasiIsoFrom.Epi P a K) (i : ℤ) :
    _root_.CategoryTheory.Epi (R.comparison.f i) := sorry

/-- The bundled model map underlying a morphism of epimorphic fixed-bound left resolutions. -/
abbrev modelHom {R S : QuasiIsoFrom.Epi P a K} (f : R ⟶ S) : R.model ⟶ S.model :=
  ObjectProperty.LeftResolution.modelHom f

/-- Morphisms of epimorphic fixed-bound left resolutions are determined by their bundled model
morphisms. -/
@[ext]
theorem hom_ext {R S : QuasiIsoFrom.Epi P a K} {f g : R ⟶ S}
    (h : modelHom f = modelHom g) : f = g := sorry

/-- The cochain map underlying a morphism of epimorphic fixed-bound left resolutions. -/
abbrev hom {R S : QuasiIsoFrom.Epi P a K} (f : R ⟶ S) : R.complex ⟶ S.complex :=
  ObjectProperty.LeftResolution.hom f

/-- The cochain map of an epimorphic fixed-bound morphism is obtained by forgetting its bundled
model morphism. -/
@[simp]
theorem hom_eq_map_modelHom {R S : QuasiIsoFrom.Epi P a K} (f : R ⟶ S) :
    hom f = (StrictlyLE.TermsIn.ι P a).map (modelHom f) := sorry

/-- The identity epimorphic fixed-bound morphism has identity bundled model morphism. -/
@[simp]
theorem id_modelHom (R : QuasiIsoFrom.Epi P a K) : modelHom (𝟙 R) = 𝟙 R.model := sorry

/-- Bundled model morphisms preserve composition of epimorphic fixed-bound morphisms. -/
@[simp]
theorem comp_modelHom {R S T : QuasiIsoFrom.Epi P a K} (f : R ⟶ S) (g : S ⟶ T) :
    modelHom (f ≫ g) = modelHom f ≫ modelHom g := sorry

/-- The identity morphism of epimorphic left resolutions induces the identity cochain map. -/
@[simp]
theorem id_hom (R : QuasiIsoFrom.Epi P a K) : hom (𝟙 R) = 𝟙 R.complex := sorry

/-- Composition of epimorphic left-resolution morphisms induces composition of cochain maps. -/
@[simp]
theorem comp_hom {R S T : QuasiIsoFrom.Epi P a K} (f : R ⟶ S) (g : S ⟶ T) :
    hom (f ≫ g) = hom f ≫ hom g := sorry

/-- A morphism of epimorphic left resolutions commutes with the comparisons. -/
@[reassoc]
theorem comparison_naturality {R S : QuasiIsoFrom.Epi P a K} (f : R ⟶ S) :
    hom f ≫ S.comparison = R.comparison := sorry

/-- The functor selecting the bundled model of an epimorphic fixed-bound left resolution. -/
abbrev modelFunctor (P : ObjectProperty A) (a : ℤ) (K : CochainComplex A ℤ) :
    QuasiIsoFrom.Epi P a K ⥤ StrictlyLE.TermsIn P a :=
  ObjectProperty.LeftResolution.modelFunctor (CochainComplex.StrictlyLE.termsIn P a)
    (HomologicalComplex.quasiIsoEpi A (ComplexShape.up ℤ)) K

/-- The epimorphic fixed-bound model functor returns the bundled model. -/
@[simp]
theorem modelFunctor_obj (R : QuasiIsoFrom.Epi P a K) :
    (modelFunctor P a K).obj R = R.model := sorry

/-- The epimorphic fixed-bound model functor retains the bundled model map. -/
@[simp]
theorem modelFunctor_map {R S : QuasiIsoFrom.Epi P a K} (f : R ⟶ S) :
    (modelFunctor P a K).map f = modelHom f := sorry

/-- The functor selecting the underlying complex of an epimorphic fixed-bound left resolution. -/
abbrev complexFunctor (P : ObjectProperty A) (a : ℤ) (K : CochainComplex A ℤ) :
    QuasiIsoFrom.Epi P a K ⥤ CochainComplex A ℤ :=
  ObjectProperty.LeftResolution.objectFunctor (CochainComplex.StrictlyLE.termsIn P a)
    (HomologicalComplex.quasiIsoEpi A (ComplexShape.up ℤ)) K

/-- The underlying-complex functor returns the resolving complex. -/
@[simp]
theorem complexFunctor_obj (R : QuasiIsoFrom.Epi P a K) :
    (complexFunctor P a K).obj R = R.complex := sorry

/-- The underlying-complex functor retains the cochain map. -/
@[simp]
theorem complexFunctor_map {R S : QuasiIsoFrom.Epi P a K} (f : R ⟶ S) :
    (complexFunctor P a K).map f = hom f := sorry

/-- Forgetting the bundled fixed-bound models identifies the epimorphic model and complex
functors. -/
theorem modelFunctor_comp_ι (P : ObjectProperty A) (a : ℤ) (K : CochainComplex A ℤ) :
    modelFunctor P a K ⋙ StrictlyLE.TermsIn.ι P a = complexFunctor P a K := sorry

/-- The comparisons of epimorphic fixed-bound left resolutions form a natural transformation. -/
abbrev comparisonNatTrans (P : ObjectProperty A) (a : ℤ) (K : CochainComplex A ℤ) :
    complexFunctor P a K ⟶ (Functor.const (QuasiIsoFrom.Epi P a K)).obj K :=
  ObjectProperty.LeftResolution.comparisonNatTrans (CochainComplex.StrictlyLE.termsIn P a)
    (HomologicalComplex.quasiIsoEpi A (ComplexShape.up ℤ)) K

/-- Evaluating the epimorphic comparison transformation gives the resolution comparison. -/
@[simp]
theorem comparisonNatTrans_app (R : QuasiIsoFrom.Epi P a K) :
    (comparisonNatTrans P a K).app R = R.comparison := sorry

/-- Forget the epimorphism condition while retaining the fixed-upper-bound left model. -/
def toQuasiIsoFrom (R : QuasiIsoFrom.Epi P a K) : QuasiIsoFrom P a K :=
  R.mapOfLE le_rfl
    (HomologicalComplex.quasiIsoEpi_le_quasiIso A (ComplexShape.up ℤ))

namespace toQuasiIsoFrom

/-- Forgetting the epimorphism condition maps morphisms of fixed-bound left resolutions. -/
abbrev hom {R S : QuasiIsoFrom.Epi P a K} (f : R ⟶ S) :
    R.toQuasiIsoFrom ⟶ S.toQuasiIsoFrom :=
  ObjectProperty.LeftResolution.mapOfLE.hom le_rfl
    (HomologicalComplex.quasiIsoEpi_le_quasiIso A (ComplexShape.up ℤ)) f

/-- Forget the epimorphism condition functorially on fixed-bound left resolutions. -/
abbrev functor (P : ObjectProperty A) (a : ℤ) (K : CochainComplex A ℤ) :
    QuasiIsoFrom.Epi P a K ⥤ QuasiIsoFrom P a K :=
  ObjectProperty.LeftResolution.mapOfLE.functor le_rfl
    (HomologicalComplex.quasiIsoEpi_le_quasiIso A (ComplexShape.up ℤ)) K

/-- The forgetful functor acts on objects by `toQuasiIsoFrom`. -/
@[simp]
theorem functor_obj (R : QuasiIsoFrom.Epi P a K) :
    (functor P a K).obj R = R.toQuasiIsoFrom := sorry

/-- The forgetful functor acts on morphisms by `toQuasiIsoFrom.hom`. -/
@[simp]
theorem functor_map {R S : QuasiIsoFrom.Epi P a K} (f : R ⟶ S) :
    (functor P a K).map f = hom f := sorry

/-- Forgetting the epimorphism condition retains the underlying cochain map. -/
@[simp]
theorem hom_hom {R S : QuasiIsoFrom.Epi P a K} (f : R ⟶ S) :
    QuasiIsoFrom.hom (hom f) = Epi.hom f := sorry

end toQuasiIsoFrom

/-- Epimorphic fixed-upper-bound left models are nonempty exactly when explicit model data with
both comparison properties exist. -/
theorem nonempty_iff :
    Nonempty (QuasiIsoFrom.Epi P a K) ↔
      ∃ (M : CochainComplex.StrictlyLE.TermsIn P a) (f : M.obj ⟶ K),
        QuasiIso f ∧ _root_.CategoryTheory.Epi f := sorry

/-- The model selected by `mk` is the supplied fixed-upper-bound complex. -/
@[simp]
theorem mk_model (M : CochainComplex.StrictlyLE.TermsIn P a) (f : M.obj ⟶ K)
    (hf : QuasiIso f) (he : _root_.CategoryTheory.Epi f) :
    (mk M f hf he).model = M := sorry

/-- The comparison selected by `mk` is the supplied epimorphic quasi-isomorphism. -/
@[simp]
theorem mk_comparison (M : CochainComplex.StrictlyLE.TermsIn P a) (f : M.obj ⟶ K)
    (hf : QuasiIso f) (he : _root_.CategoryTheory.Epi f) :
    (mk M f hf he).comparison = f := sorry

/-- Forgetting epimorphism data preserves the model. -/
@[simp]
theorem toQuasiIsoFrom_model (R : QuasiIsoFrom.Epi P a K) :
    R.toQuasiIsoFrom.model = R.model := sorry

/-- Forgetting epimorphism data preserves the comparison. -/
@[simp]
theorem toQuasiIsoFrom_comparison (R : QuasiIsoFrom.Epi P a K) :
    R.toQuasiIsoFrom.comparison = R.comparison := sorry

end Epi

end CochainComplex.StrictlyLE.TermsIn.QuasiIsoFrom


