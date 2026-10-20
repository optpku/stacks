/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.Algebra.Homology.CochainComplex.Bounded.Termwise.Minus.Localization
public import ReasLib.Algebra.Homology.CochainComplex.BoundedAboveReplacement.Predicate
public import ReasLib.CategoryTheory.Localization.LocalizerMorphism.Resolution.Left
public import Mathlib.Tactic.CrossRefAttribute

/-!
# Bounded-Above Termwise Models with a Variable Bound

This leaf packages quasi-isomorphisms from `Minus.TermsIn P` as Mathlib left resolutions.  Unlike
the fixed-bound owner in `BoundedAboveReplacement.Resolution`, the cutoff is not part of the data;
the model merely carries the canonical bounded-above structure.
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits

universe v u

namespace CochainComplex.Minus.TermsIn

variable {A : Type u} [Category.{v} A] [HasZeroMorphisms A] [CategoryWithHomology A]

/-- Quasi-isomorphisms between bounded-above termwise-`P` models, detected by their underlying
cochain maps. -/
@[stacks 05T7 "quasi-isomorphisms between bounded-above termwise models"]
abbrev quasiIso (P : ObjectProperty A) : MorphismProperty (Minus.TermsIn P) :=
  (HomologicalComplex.quasiIso A (ComplexShape.up ℤ)).inverseImage (ι P)

/-- The localizer morphism induced by the inclusion of bounded-above termwise-`P` complexes. -/
@[stacks 05T7 "localizer morphism for bounded-above termwise models"]
abbrev localizer (P : ObjectProperty A) :
    LocalizerMorphism (quasiIso P)
      (HomologicalComplex.quasiIso A (ComplexShape.up ℤ)) :=
  (localizerOnMinus A P).comp (Minus.localizer A)

/-- A quasi-isomorphism from a bounded-above complex whose terms satisfy `P` to `K`. -/
@[stacks 05T7 "variable-upper-bound property-indexed resolution"]
abbrev QuasiIsoFrom (P : ObjectProperty A) (K : CochainComplex A ℤ) :=
  (localizer P).LeftResolution K

namespace QuasiIsoFrom

variable {P : ObjectProperty A} {K : CochainComplex A ℤ}

/-- Construct a bounded-above termwise left model from explicit comparison data. -/
def mk (M : Minus.TermsIn P) (f : (M : CochainComplex A ℤ) ⟶ K) (hf : QuasiIso f) :
    QuasiIsoFrom P K where
  X₁ := M
  w := f
  hw := hf

/-- The bundled bounded-above termwise model. -/
abbrev model (R : QuasiIsoFrom P K) : Minus.TermsIn P :=
  LocalizerMorphism.LeftResolution.model R

/-- The cochain complex underlying a bounded-above termwise left model. -/
abbrev complex (R : QuasiIsoFrom P K) : CochainComplex A ℤ :=
  (Minus.TermsIn.ι P).obj R.model

/-- The quasi-isomorphic comparison from the left model to the original complex. -/
abbrev comparison (R : QuasiIsoFrom P K) : R.complex ⟶ K :=
  LocalizerMorphism.LeftResolution.comparison R

/-- Conventional name for the comparison from a bounded-above left model. -/
abbrev π (R : QuasiIsoFrom P K) : R.complex ⟶ K :=
  R.comparison

/-- A bounded-above left model coerces to its bundled termwise model. -/
instance : CoeOut (QuasiIsoFrom P K) (Minus.TermsIn P) where
  coe R := R.model

/-- A bounded-above left model coerces to its bundled bounded-above complex. -/
instance : CoeOut (QuasiIsoFrom P K) (Minus A) where
  coe R := R.model

/-- A bounded-above left model coerces to its underlying cochain complex. -/
instance : CoeOut (QuasiIsoFrom P K) (CochainComplex A ℤ) where
  coe R := R.complex

/-- The resolving complex is bounded above. -/
theorem minus (R : QuasiIsoFrom P K) : CochainComplex.minus A R.complex := sorry

/-- The resolving complex vanishes in all sufficiently positive degrees. -/
theorem exists_isStrictlyLE (R : QuasiIsoFrom P K) :
    ∃ a : ℤ, R.complex.IsStrictlyLE a := sorry

/-- Every term of the resolving complex satisfies the chosen object property. -/
theorem term_mem (R : QuasiIsoFrom P K) (n : ℤ) : P (R.complex.X n) := sorry

/-- The comparison from a bounded-above left model is a quasi-isomorphism. -/
instance comparison_quasiIso (R : QuasiIsoFrom P K) : QuasiIso R.comparison := sorry

/-- The morphism of bundled models underlying a morphism of left resolutions. -/
abbrev modelHom {R S : QuasiIsoFrom P K} (f : R ⟶ S) : R.model ⟶ S.model :=
  LocalizerMorphism.LeftResolution.modelHom f

/-- Morphisms of variable-upper-bound left resolutions are determined by their morphisms of
bundled models. -/
@[ext]
theorem hom_ext {R S : QuasiIsoFrom P K} {f g : R ⟶ S}
    (h : modelHom f = modelHom g) : f = g := sorry

/-- The cochain map underlying a morphism of bounded-above left resolutions. -/
abbrev hom {R S : QuasiIsoFrom P K} (f : R ⟶ S) : R.complex ⟶ S.complex :=
  LocalizerMorphism.LeftResolution.hom f

/-- The cochain map of a left-resolution morphism is obtained by forgetting its bundled model
morphism. -/
@[simp]
theorem hom_eq_map_modelHom {R S : QuasiIsoFrom P K} (f : R ⟶ S) :
    hom f = (Minus.TermsIn.ι P).map (modelHom f) := sorry

/-- The identity left-resolution morphism has identity bundled model morphism. -/
@[simp]
theorem id_modelHom (R : QuasiIsoFrom P K) : modelHom (𝟙 R) = 𝟙 R.model := sorry

/-- Bundled model morphisms preserve composition of left-resolution morphisms. -/
@[simp]
theorem comp_modelHom {R S T : QuasiIsoFrom P K} (f : R ⟶ S) (g : S ⟶ T) :
    modelHom (f ≫ g) = modelHom f ≫ modelHom g := sorry

/-- The identity left-resolution morphism induces the identity cochain map. -/
@[simp]
theorem id_hom (R : QuasiIsoFrom P K) : hom (𝟙 R) = 𝟙 R.complex := sorry

/-- Underlying cochain maps preserve composition of left-resolution morphisms. -/
@[simp]
theorem comp_hom {R S T : QuasiIsoFrom P K} (f : R ⟶ S) (g : S ⟶ T) :
    hom (f ≫ g) = hom f ≫ hom g := sorry

/-- A morphism of bounded-above left resolutions commutes with the comparisons. -/
@[reassoc]
theorem comparison_naturality {R S : QuasiIsoFrom P K} (f : R ⟶ S) :
    hom f ≫ S.comparison = R.comparison := sorry

/-- The functor selecting the bundled bounded-above model of a left resolution. -/
abbrev modelFunctor (P : ObjectProperty A) (K : CochainComplex A ℤ) :
    QuasiIsoFrom P K ⥤ Minus.TermsIn P :=
  LocalizerMorphism.LeftResolution.modelFunctor (localizer P) K

/-- The variable-upper-bound model functor returns the bundled resolving model. -/
@[simp]
theorem modelFunctor_obj (R : QuasiIsoFrom P K) : (modelFunctor P K).obj R = R.model := sorry

/-- The variable-upper-bound model functor retains the bundled model morphism. -/
@[simp]
theorem modelFunctor_map {R S : QuasiIsoFrom P K} (f : R ⟶ S) :
    (modelFunctor P K).map f = modelHom f := sorry

/-- The functor selecting the underlying cochain complex of a left resolution. -/
abbrev complexFunctor (P : ObjectProperty A) (K : CochainComplex A ℤ) :
    QuasiIsoFrom P K ⥤ CochainComplex A ℤ :=
  LocalizerMorphism.LeftResolution.objectFunctor (localizer P) K

/-- The underlying-complex functor returns the resolving cochain complex. -/
@[simp]
theorem complexFunctor_obj (R : QuasiIsoFrom P K) :
    (complexFunctor P K).obj R = R.complex := sorry

/-- The underlying-complex functor retains the cochain map of a resolution morphism. -/
@[simp]
theorem complexFunctor_map {R S : QuasiIsoFrom P K} (f : R ⟶ S) :
    (complexFunctor P K).map f = hom f := sorry

/-- Forgetting the bundled termwise models identifies the model and complex functors. -/
theorem modelFunctor_comp_ι (P : ObjectProperty A) (K : CochainComplex A ℤ) :
    modelFunctor P K ⋙ Minus.TermsIn.ι P = complexFunctor P K := sorry

/-- The comparisons from bounded-above models form a natural transformation. -/
abbrev comparisonNatTrans (P : ObjectProperty A) (K : CochainComplex A ℤ) :
    complexFunctor P K ⟶ (Functor.const (QuasiIsoFrom P K)).obj K :=
  LocalizerMorphism.LeftResolution.comparisonNatTrans (localizer P) K

/-- Evaluating the comparison transformation gives the left-resolution comparison. -/
@[simp]
theorem comparisonNatTrans_app (R : QuasiIsoFrom P K) :
    (comparisonNatTrans P K).app R = R.comparison := sorry

/-- Variable-bound left resolutions are nonempty exactly when explicit model data exist. -/
theorem nonempty_iff :
    Nonempty (QuasiIsoFrom P K) ↔
      ∃ (M : Minus.TermsIn P) (f : (M : CochainComplex A ℤ) ⟶ K), QuasiIso f := sorry

/-- The named constructor retains the supplied bundled model. -/
@[simp]
theorem mk_model (M : Minus.TermsIn P) (f : (M : CochainComplex A ℤ) ⟶ K)
    (hf : QuasiIso f) :
    (mk M f hf).model = M := sorry

/-- The named constructor retains the supplied comparison. -/
@[simp]
theorem mk_comparison (M : Minus.TermsIn P) (f : (M : CochainComplex A ℤ) ⟶ K)
    (hf : QuasiIso f) :
    (mk M f hf).comparison = f := sorry

end QuasiIsoFrom

end CochainComplex.Minus.TermsIn


