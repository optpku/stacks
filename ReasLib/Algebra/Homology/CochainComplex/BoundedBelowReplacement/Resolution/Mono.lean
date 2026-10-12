/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import ReasLib.Algebra.Homology.CochainComplex.BoundedBelowReplacement.Resolution
public import ReasLib.Algebra.Homology.HomologicalComplex.MonoEpi
public import ReasLib.Algebra.Homology.HomologicalComplex.QuasiIso.MonoEpi
public import ReasLib.CategoryTheory.ObjectProperty.Localization.Resolution.Right.Monotonicity
public import Mathlib.Tactic.CrossRefAttribute

/-!
# Monomorphic Quasi-Isomorphic Models with a Fixed Lower Bound

This file refines fixed-lower-bound right models by requiring the comparison to be a
monomorphism in the category of complexes.  Degreewise monomorphisms are exposed as a derived
API when the ambient category has pullbacks.
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits

universe v u

namespace CochainComplex.StrictlyGE.TermsIn.QuasiIsoTo

variable {A : Type u} [Category.{v} A] [HasZeroMorphisms A] [CategoryWithHomology A]

/-- A monomorphic quasi-isomorphism from `K` to a complex strictly bounded below at `a` whose
terms satisfy `P`.  The denominator is the intersection of quasi-isomorphisms and categorical
monomorphisms. -/
@[stacks 05T6 "monomorphic fixed-lower-bound property-indexed resolution"]
abbrev Mono (P : ObjectProperty A) (a : ℤ) (K : CochainComplex A ℤ) :=
  ObjectProperty.RightResolution (CochainComplex.StrictlyGE.termsIn P a)
    (HomologicalComplex.quasiIsoMono A (ComplexShape.up ℤ)) K

namespace Mono

variable {P : ObjectProperty A} {a : ℤ} {K : CochainComplex A ℤ}

/-- Construct a monomorphic fixed-lower-bound model from explicit comparison data. -/
def mk (M : CochainComplex.StrictlyGE.TermsIn P a) (f : K ⟶ M.obj)
    (hf : QuasiIso f) (hm : _root_.CategoryTheory.Mono f) : QuasiIsoTo.Mono P a K :=
  ObjectProperty.RightResolution.mk M f ⟨hf, hm⟩

/-- The bundled fixed-lower-bound termwise model. -/
abbrev model (R : QuasiIsoTo.Mono P a K) : CochainComplex.StrictlyGE.TermsIn P a :=
  ObjectProperty.RightResolution.model R

/-- The cochain complex underlying a monomorphic right model. -/
abbrev complex (R : QuasiIsoTo.Mono P a K) : CochainComplex A ℤ :=
  ObjectProperty.RightResolution.object R

/-- The monomorphic quasi-isomorphism from the original complex to the model. -/
abbrev comparison (R : QuasiIsoTo.Mono P a K) : K ⟶ R.complex :=
  ObjectProperty.RightResolution.comparison R

/-- Conventional name for the comparison into a monomorphic right model. -/
abbrev ι (R : QuasiIsoTo.Mono P a K) : K ⟶ R.complex :=
  R.comparison

/-- A monomorphic fixed-lower-bound right model coerces to its underlying complex. -/
instance : CoeOut (QuasiIsoTo.Mono P a K) (CochainComplex A ℤ) where
  coe R := R.complex

/-- The model retains the specified strict lower bound. -/
instance complex_isStrictlyGE (R : QuasiIsoTo.Mono P a K) : R.complex.IsStrictlyGE a := sorry

/-- Every term of the model satisfies the chosen object property. -/
theorem term_mem (R : QuasiIsoTo.Mono P a K) (i : ℤ) : P (R.complex.X i) := sorry

/-- The comparison into the model is a quasi-isomorphism. -/
instance comparison_quasiIso (R : QuasiIsoTo.Mono P a K) : QuasiIso R.comparison := sorry

/-- The comparison into the model is a monomorphism of complexes. -/
instance comparison_mono (R : QuasiIsoTo.Mono P a K) :
    _root_.CategoryTheory.Mono R.comparison := sorry

/-- With pullbacks, every component of the comparison is monomorphic. -/
theorem comparison_mono_f [HasPullbacks A] (R : QuasiIsoTo.Mono P a K) (i : ℤ) :
    _root_.CategoryTheory.Mono (R.comparison.f i) := sorry

/-- The bundled model map underlying a morphism of monomorphic fixed-bound right resolutions. -/
abbrev modelHom {R S : QuasiIsoTo.Mono P a K} (f : R ⟶ S) : R.model ⟶ S.model :=
  ObjectProperty.RightResolution.modelHom f

/-- Morphisms of monomorphic fixed-bound right resolutions are determined by their bundled
model morphisms. -/
@[ext]
theorem hom_ext {R S : QuasiIsoTo.Mono P a K} {f g : R ⟶ S}
    (h : modelHom f = modelHom g) : f = g := sorry

/-- The cochain map underlying a morphism of monomorphic fixed-bound right resolutions. -/
abbrev hom {R S : QuasiIsoTo.Mono P a K} (f : R ⟶ S) : R.complex ⟶ S.complex :=
  ObjectProperty.RightResolution.hom f

/-- The cochain map of a monomorphic fixed-bound morphism is obtained by forgetting its bundled
model morphism. -/
@[simp]
theorem hom_eq_map_modelHom {R S : QuasiIsoTo.Mono P a K} (f : R ⟶ S) :
    hom f = (StrictlyGE.TermsIn.ι P a).map (modelHom f) := sorry

/-- The identity monomorphic fixed-bound morphism has identity bundled model morphism. -/
@[simp]
theorem id_modelHom (R : QuasiIsoTo.Mono P a K) : modelHom (𝟙 R) = 𝟙 R.model := sorry

/-- Bundled model morphisms preserve composition of monomorphic fixed-bound morphisms. -/
@[simp]
theorem comp_modelHom {R S T : QuasiIsoTo.Mono P a K} (f : R ⟶ S) (g : S ⟶ T) :
    modelHom (f ≫ g) = modelHom f ≫ modelHom g := sorry

/-- The identity morphism of monomorphic right resolutions induces the identity cochain map. -/
@[simp]
theorem id_hom (R : QuasiIsoTo.Mono P a K) : hom (𝟙 R) = 𝟙 R.complex := sorry

/-- Composition of monomorphic right-resolution morphisms induces composition of cochain maps. -/
@[simp]
theorem comp_hom {R S T : QuasiIsoTo.Mono P a K} (f : R ⟶ S) (g : S ⟶ T) :
    hom (f ≫ g) = hom f ≫ hom g := sorry

/-- A morphism of monomorphic right resolutions commutes with the comparisons. -/
@[reassoc]
theorem comparison_naturality {R S : QuasiIsoTo.Mono P a K} (f : R ⟶ S) :
    R.comparison ≫ hom f = S.comparison := sorry

/-- The functor selecting the bundled model of a monomorphic fixed-bound right resolution. -/
abbrev modelFunctor (P : ObjectProperty A) (a : ℤ) (K : CochainComplex A ℤ) :
    QuasiIsoTo.Mono P a K ⥤ StrictlyGE.TermsIn P a :=
  ObjectProperty.RightResolution.modelFunctor (CochainComplex.StrictlyGE.termsIn P a)
    (HomologicalComplex.quasiIsoMono A (ComplexShape.up ℤ)) K

/-- The monomorphic fixed-bound model functor returns the bundled model. -/
@[simp]
theorem modelFunctor_obj (R : QuasiIsoTo.Mono P a K) :
    (modelFunctor P a K).obj R = R.model := sorry

/-- The monomorphic fixed-bound model functor retains the bundled model map. -/
@[simp]
theorem modelFunctor_map {R S : QuasiIsoTo.Mono P a K} (f : R ⟶ S) :
    (modelFunctor P a K).map f = modelHom f := sorry

/-- The functor selecting the underlying complex of a monomorphic fixed-bound right resolution. -/
abbrev complexFunctor (P : ObjectProperty A) (a : ℤ) (K : CochainComplex A ℤ) :
    QuasiIsoTo.Mono P a K ⥤ CochainComplex A ℤ :=
  ObjectProperty.RightResolution.objectFunctor (CochainComplex.StrictlyGE.termsIn P a)
    (HomologicalComplex.quasiIsoMono A (ComplexShape.up ℤ)) K

/-- The underlying-complex functor returns the resolving complex. -/
@[simp]
theorem complexFunctor_obj (R : QuasiIsoTo.Mono P a K) :
    (complexFunctor P a K).obj R = R.complex := sorry

/-- The underlying-complex functor retains the cochain map. -/
@[simp]
theorem complexFunctor_map {R S : QuasiIsoTo.Mono P a K} (f : R ⟶ S) :
    (complexFunctor P a K).map f = hom f := sorry

/-- Forgetting the bundled fixed-bound models identifies the monomorphic model and complex
functors. -/
theorem modelFunctor_comp_ι (P : ObjectProperty A) (a : ℤ) (K : CochainComplex A ℤ) :
    modelFunctor P a K ⋙ StrictlyGE.TermsIn.ι P a = complexFunctor P a K := sorry

/-- The comparisons of monomorphic fixed-bound right resolutions form a natural
transformation. -/
abbrev comparisonNatTrans (P : ObjectProperty A) (a : ℤ) (K : CochainComplex A ℤ) :
    (Functor.const (QuasiIsoTo.Mono P a K)).obj K ⟶ complexFunctor P a K :=
  ObjectProperty.RightResolution.comparisonNatTrans (CochainComplex.StrictlyGE.termsIn P a)
    (HomologicalComplex.quasiIsoMono A (ComplexShape.up ℤ)) K

/-- Evaluating the monomorphic comparison transformation gives the resolution comparison. -/
@[simp]
theorem comparisonNatTrans_app (R : QuasiIsoTo.Mono P a K) :
    (comparisonNatTrans P a K).app R = R.comparison := sorry

/-- Forget the monomorphism condition while retaining the fixed-lower-bound right model. -/
def toQuasiIsoTo (R : QuasiIsoTo.Mono P a K) : QuasiIsoTo P a K :=
  R.mapOfLE le_rfl
    (HomologicalComplex.quasiIsoMono_le_quasiIso A (ComplexShape.up ℤ))

namespace toQuasiIsoTo

/-- Forgetting the monomorphism condition maps morphisms of fixed-bound right resolutions. -/
abbrev hom {R S : QuasiIsoTo.Mono P a K} (f : R ⟶ S) :
    R.toQuasiIsoTo ⟶ S.toQuasiIsoTo :=
  ObjectProperty.RightResolution.mapOfLE.hom le_rfl
    (HomologicalComplex.quasiIsoMono_le_quasiIso A (ComplexShape.up ℤ)) f

/-- Forget the monomorphism condition functorially on fixed-bound right resolutions. -/
abbrev functor (P : ObjectProperty A) (a : ℤ) (K : CochainComplex A ℤ) :
    QuasiIsoTo.Mono P a K ⥤ QuasiIsoTo P a K :=
  ObjectProperty.RightResolution.mapOfLE.functor le_rfl
    (HomologicalComplex.quasiIsoMono_le_quasiIso A (ComplexShape.up ℤ)) K

/-- The forgetful functor acts on objects by `toQuasiIsoTo`. -/
@[simp]
theorem functor_obj (R : QuasiIsoTo.Mono P a K) :
    (functor P a K).obj R = R.toQuasiIsoTo := sorry

/-- The forgetful functor acts on morphisms by `toQuasiIsoTo.hom`. -/
@[simp]
theorem functor_map {R S : QuasiIsoTo.Mono P a K} (f : R ⟶ S) :
    (functor P a K).map f = hom f := sorry

/-- Forgetting the monomorphism condition retains the underlying cochain map. -/
@[simp]
theorem hom_hom {R S : QuasiIsoTo.Mono P a K} (f : R ⟶ S) :
    QuasiIsoTo.hom (hom f) = Mono.hom f := sorry

end toQuasiIsoTo

/-- Monomorphic fixed-lower-bound right models are nonempty exactly when explicit model data
with both comparison properties exist. -/
theorem nonempty_iff :
    Nonempty (QuasiIsoTo.Mono P a K) ↔
      ∃ (M : CochainComplex.StrictlyGE.TermsIn P a) (f : K ⟶ M.obj),
        QuasiIso f ∧ _root_.CategoryTheory.Mono f := sorry

/-- The model selected by `mk` is the supplied fixed-lower-bound complex. -/
@[simp]
theorem mk_model (M : CochainComplex.StrictlyGE.TermsIn P a) (f : K ⟶ M.obj)
    (hf : QuasiIso f) (hm : _root_.CategoryTheory.Mono f) :
    (mk M f hf hm).model = M := sorry

/-- The comparison selected by `mk` is the supplied monomorphic quasi-isomorphism. -/
@[simp]
theorem mk_comparison (M : CochainComplex.StrictlyGE.TermsIn P a) (f : K ⟶ M.obj)
    (hf : QuasiIso f) (hm : _root_.CategoryTheory.Mono f) :
    (mk M f hf hm).comparison = f := sorry

/-- Forgetting monomorphism data preserves the model. -/
@[simp]
theorem toQuasiIsoTo_model (R : QuasiIsoTo.Mono P a K) :
    R.toQuasiIsoTo.model = R.model := sorry

/-- Forgetting monomorphism data preserves the comparison. -/
@[simp]
theorem toQuasiIsoTo_comparison (R : QuasiIsoTo.Mono P a K) :
    R.toQuasiIsoTo.comparison = R.comparison := sorry

end Mono

end CochainComplex.StrictlyGE.TermsIn.QuasiIsoTo


