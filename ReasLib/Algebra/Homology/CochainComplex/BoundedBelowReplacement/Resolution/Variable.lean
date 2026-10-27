/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.Algebra.Homology.CochainComplex.Bounded.Termwise.Plus.Localization
public import ReasLib.Algebra.Homology.CochainComplex.BoundedBelowReplacement.Predicate
public import ReasLib.CategoryTheory.Localization.LocalizerMorphism.Resolution.Right
public import Mathlib.Tactic.CrossRefAttribute

/-!
# Bounded-Below Termwise Models with a Variable Bound

This leaf packages quasi-isomorphisms into `Plus.TermsIn P` as Mathlib right resolutions.  Unlike
the fixed-bound owner in `BoundedBelowReplacement.Resolution`, the cutoff is not part of the data;
the model merely carries the canonical bounded-below structure.
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits

universe v u

namespace CochainComplex.Plus.TermsIn

variable {A : Type u} [Category.{v} A] [HasZeroMorphisms A] [CategoryWithHomology A]

/-- Quasi-isomorphisms between bounded-below termwise-`P` models, detected by their underlying
cochain maps. -/
@[stacks 05T6 "quasi-isomorphisms between bounded-below termwise models"]
abbrev quasiIso (P : ObjectProperty A) : MorphismProperty (Plus.TermsIn P) :=
  (HomologicalComplex.quasiIso A (ComplexShape.up ℤ)).inverseImage (ι P)

/-- The localizer morphism induced by the inclusion of bounded-below termwise-`P` complexes. -/
@[stacks 05T6 "localizer morphism for bounded-below termwise models"]
abbrev localizer (P : ObjectProperty A) :
    LocalizerMorphism (quasiIso P)
      (HomologicalComplex.quasiIso A (ComplexShape.up ℤ)) :=
  (localizerOnPlus A P).comp (Plus.localizer A)

/-- A quasi-isomorphism from `K` to a bounded-below complex whose terms satisfy `P`. -/
@[stacks 05T6 "variable-lower-bound property-indexed resolution"]
abbrev QuasiIsoTo (P : ObjectProperty A) (K : CochainComplex A ℤ) :=
  (localizer P).RightResolution K

namespace QuasiIsoTo

variable {P : ObjectProperty A} {K : CochainComplex A ℤ}

/-- Construct a bounded-below termwise right model from explicit comparison data. -/
def mk (M : Plus.TermsIn P) (f : K ⟶ (M : CochainComplex A ℤ)) (hf : QuasiIso f) :
    QuasiIsoTo P K where
  X₁ := M
  w := f
  hw := hf

/-- The bundled bounded-below termwise model. -/
abbrev model (R : QuasiIsoTo P K) : Plus.TermsIn P :=
  LocalizerMorphism.RightResolution.model R

/-- The cochain complex underlying a bounded-below termwise right model. -/
abbrev complex (R : QuasiIsoTo P K) : CochainComplex A ℤ :=
  (Plus.TermsIn.ι P).obj R.model

/-- The quasi-isomorphic comparison from the original complex to the right model. -/
abbrev comparison (R : QuasiIsoTo P K) : K ⟶ R.complex :=
  LocalizerMorphism.RightResolution.comparison R

/-- Conventional name for the comparison into a bounded-below right model. -/
abbrev ι (R : QuasiIsoTo P K) : K ⟶ R.complex :=
  R.comparison

/-- A bounded-below right model coerces to its bundled termwise model. -/
instance : CoeOut (QuasiIsoTo P K) (Plus.TermsIn P) where
  coe R := R.model

/-- A bounded-below right model coerces to its bundled bounded-below complex. -/
instance : CoeOut (QuasiIsoTo P K) (Plus A) where
  coe R := R.model

/-- A bounded-below right model coerces to its underlying cochain complex. -/
instance : CoeOut (QuasiIsoTo P K) (CochainComplex A ℤ) where
  coe R := R.complex

/-- The resolving complex is bounded below. -/
theorem plus (R : QuasiIsoTo P K) : CochainComplex.plus A R.complex :=
  R.model.obj.property

/-- The resolving complex vanishes in all sufficiently negative degrees. -/
theorem exists_isStrictlyGE (R : QuasiIsoTo P K) :
    ∃ a : ℤ, R.complex.IsStrictlyGE a :=
  R.plus

/-- Every term of the resolving complex satisfies the chosen object property. -/
theorem term_mem (R : QuasiIsoTo P K) (n : ℤ) : P (R.complex.X n) :=
  R.model.property n

/-- The comparison into a bounded-below right model is a quasi-isomorphism. -/
instance comparison_quasiIso (R : QuasiIsoTo P K) : QuasiIso R.comparison :=
  R.hw

/-- The morphism of bundled models underlying a morphism of right resolutions. -/
abbrev modelHom {R S : QuasiIsoTo P K} (f : R ⟶ S) : R.model ⟶ S.model :=
  LocalizerMorphism.RightResolution.modelHom f

/-- Morphisms of variable-lower-bound right resolutions are determined by their morphisms of
bundled models. -/
@[ext]
theorem hom_ext {R S : QuasiIsoTo P K} {f g : R ⟶ S}
    (h : modelHom f = modelHom g) : f = g :=
  LocalizerMorphism.RightResolution.hom_ext h

/-- The cochain map underlying a morphism of bounded-below right resolutions. -/
abbrev hom {R S : QuasiIsoTo P K} (f : R ⟶ S) : R.complex ⟶ S.complex :=
  LocalizerMorphism.RightResolution.hom f

/-- The cochain map of a right-resolution morphism is obtained by forgetting its bundled
model morphism. -/
@[simp]
theorem hom_eq_map_modelHom {R S : QuasiIsoTo P K} (f : R ⟶ S) :
    hom f = (Plus.TermsIn.ι P).map (modelHom f) := rfl

/-- The identity right-resolution morphism has identity bundled model morphism. -/
@[simp]
theorem id_modelHom (R : QuasiIsoTo P K) : modelHom (𝟙 R) = 𝟙 R.model := rfl

/-- Bundled model morphisms preserve composition of right-resolution morphisms. -/
@[simp]
theorem comp_modelHom {R S T : QuasiIsoTo P K} (f : R ⟶ S) (g : S ⟶ T) :
    modelHom (f ≫ g) = modelHom f ≫ modelHom g := rfl

/-- The identity right-resolution morphism induces the identity cochain map. -/
@[simp]
theorem id_hom (R : QuasiIsoTo P K) : hom (𝟙 R) = 𝟙 R.complex :=
  (Plus.TermsIn.ι P).map_id R.model

/-- Underlying cochain maps preserve composition of right-resolution morphisms. -/
@[simp]
theorem comp_hom {R S T : QuasiIsoTo P K} (f : R ⟶ S) (g : S ⟶ T) :
    hom (f ≫ g) = hom f ≫ hom g :=
  (Plus.TermsIn.ι P).map_comp (modelHom f) (modelHom g)

/-- A morphism of bounded-below right resolutions commutes with the comparisons. -/
@[reassoc]
theorem comparison_naturality {R S : QuasiIsoTo P K} (f : R ⟶ S) :
    R.comparison ≫ hom f = S.comparison :=
  f.comm

/-- The functor selecting the bundled bounded-below model of a right resolution. -/
abbrev modelFunctor (P : ObjectProperty A) (K : CochainComplex A ℤ) :
    QuasiIsoTo P K ⥤ Plus.TermsIn P :=
  LocalizerMorphism.RightResolution.modelFunctor (localizer P) K

/-- The variable-lower-bound model functor returns the bundled resolving model. -/
@[simp]
theorem modelFunctor_obj (R : QuasiIsoTo P K) : (modelFunctor P K).obj R = R.model := rfl

/-- The variable-lower-bound model functor retains the bundled model morphism. -/
@[simp]
theorem modelFunctor_map {R S : QuasiIsoTo P K} (f : R ⟶ S) :
    (modelFunctor P K).map f = modelHom f := rfl

/-- The functor selecting the underlying cochain complex of a right resolution. -/
abbrev complexFunctor (P : ObjectProperty A) (K : CochainComplex A ℤ) :
    QuasiIsoTo P K ⥤ CochainComplex A ℤ :=
  LocalizerMorphism.RightResolution.objectFunctor (localizer P) K

/-- The underlying-complex functor returns the resolving cochain complex. -/
@[simp]
theorem complexFunctor_obj (R : QuasiIsoTo P K) :
    (complexFunctor P K).obj R = R.complex := rfl

/-- The underlying-complex functor retains the cochain map of a resolution morphism. -/
@[simp]
theorem complexFunctor_map {R S : QuasiIsoTo P K} (f : R ⟶ S) :
    (complexFunctor P K).map f = hom f := rfl

/-- Forgetting the bundled termwise models identifies the model and complex functors. -/
theorem modelFunctor_comp_ι (P : ObjectProperty A) (K : CochainComplex A ℤ) :
    modelFunctor P K ⋙ Plus.TermsIn.ι P = complexFunctor P K := rfl

/-- The comparisons into bounded-below models form a natural transformation. -/
abbrev comparisonNatTrans (P : ObjectProperty A) (K : CochainComplex A ℤ) :
    (Functor.const (QuasiIsoTo P K)).obj K ⟶ complexFunctor P K :=
  LocalizerMorphism.RightResolution.comparisonNatTrans (localizer P) K

/-- Evaluating the comparison transformation gives the right-resolution comparison. -/
@[simp]
theorem comparisonNatTrans_app (R : QuasiIsoTo P K) :
    (comparisonNatTrans P K).app R = R.comparison := rfl

/-- Variable-bound right resolutions are nonempty exactly when explicit model data exist. -/
theorem nonempty_iff :
    Nonempty (QuasiIsoTo P K) ↔
      ∃ (M : Plus.TermsIn P) (f : K ⟶ (M : CochainComplex A ℤ)), QuasiIso f := by
  constructor
  · show Nonempty (QuasiIsoTo P K) → _
    rintro ⟨R⟩
    exact ⟨R.model, R.comparison, R.hw⟩
  · show (∃ (M : Plus.TermsIn P) (f : K ⟶ (M : CochainComplex A ℤ)), QuasiIso f) → _
    rintro ⟨M, f, hf⟩
    exact ⟨mk M f hf⟩

/-- The named constructor retains the supplied bundled model. -/
@[simp]
theorem mk_model (M : Plus.TermsIn P) (f : K ⟶ (M : CochainComplex A ℤ))
    (hf : QuasiIso f) :
    (mk M f hf).model = M := rfl

/-- The named constructor retains the supplied comparison. -/
@[simp]
theorem mk_comparison (M : Plus.TermsIn P) (f : K ⟶ (M : CochainComplex A ℤ))
    (hf : QuasiIso f) :
    (mk M f hf).comparison = f := rfl

end QuasiIsoTo

end CochainComplex.Plus.TermsIn


