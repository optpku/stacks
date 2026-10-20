/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import Mathlib.Algebra.Homology.HomotopyCategory.KInjective
public import Mathlib.CategoryTheory.Preadditive.Injective.Basic
public import Mathlib.Tactic.CrossRefAttribute
public import ReasLib.Algebra.Homology.CochainComplex.BoundedBelowReplacement.Resolution.Variable

@[expose] public section

/-!
# Injective Resolutions of Cochain Complexes

This module defines injective resolutions at the cochain-complex level: a quasi-isomorphism
from a given cochain complex to a bounded-below complex of injective objects.

This is distinct from Mathlib's `InjectiveResolution` (which is for objects of abelian
categories). Here the source is already a cochain complex.  The property-neutral bounded-below
replacement layer is in `BoundedBelowReplacement`.

## Main definitions

* `CochainComplex.InjectivePlus` — bounded-below cochain complexes of injective objects.
* `CochainComplex.InjectiveResolution` — a quasi-iso from `K` to a bounded-below injective
  complex.

## Main results

* `CochainComplex.Plus.TermsIn.instIsKInjective` — a bounded-below complex of injectives
  is K-injective.
-/

open CategoryTheory
open CategoryTheory.Limits
open CategoryTheory.ObjectProperty

universe v u

namespace CochainComplex

variable {𝒜 : Type u} [Category.{v} 𝒜] [Abelian 𝒜]

/-- The bounded-below cochain complexes whose terms are injective objects. -/
@[stacks 013I "bounded-below complexes of injective objects"]
abbrev InjectivePlus (𝒜 : Type u) [Category.{v} 𝒜] [Abelian 𝒜] :=
  CochainComplex.Plus.TermsIn (isInjective 𝒜)

namespace InjectivePlus

/-- The canonical inclusion of bounded-below termwise-injective cochain
complexes into all cochain complexes. -/
@[stacks 013I "inclusion of bounded-below injective complexes"]
abbrev ι (𝒜 : Type u) [Category.{v} 𝒜] [Abelian 𝒜] :
    InjectivePlus 𝒜 ⥤ CochainComplex 𝒜 ℤ :=
  Plus.TermsIn.ι (isInjective 𝒜)

end InjectivePlus

namespace Plus.TermsIn

/-- A bounded-below cochain complex of injective objects is K-injective. -/
@[stacks 013R]
instance instIsKInjective (I : Plus.TermsIn (isInjective 𝒜)) :
    CochainComplex.IsKInjective (I : CochainComplex 𝒜 ℤ) := by
  obtain ⟨a, ha⟩ := I.exists_bound
  exact @isKInjective_of_injective 𝒜 _ _ (I : CochainComplex 𝒜 ℤ) a ha
    (fun n ↦ I.term_mem n)

end Plus.TermsIn

/-- An injective resolution of a cochain complex is Mathlib's right resolution along the
inclusion of bounded-below termwise-injective complexes and quasi-isomorphisms. -/
@[stacks 013I "bounded-below injective right resolution"]
abbrev InjectiveResolution (K : CochainComplex 𝒜 ℤ) :=
  Plus.TermsIn.QuasiIsoTo (isInjective 𝒜) K

namespace InjectiveResolution

/-- Construct an injective resolution from an explicit bounded-below injective complex and
quasi-isomorphism. -/
def mk {K : CochainComplex 𝒜 ℤ} (I : InjectivePlus 𝒜)
    (f : K ⟶ (I : CochainComplex 𝒜 ℤ)) (hf : QuasiIso f) : InjectiveResolution K :=
  Plus.TermsIn.QuasiIsoTo.mk I f hf

/-- The bounded-below injective model underlying an injective resolution. -/
abbrev model {K : CochainComplex 𝒜 ℤ} (I : InjectiveResolution K) : InjectivePlus 𝒜 :=
  Plus.TermsIn.QuasiIsoTo.model I

/-- The cochain complex underlying an injective resolution. -/
abbrev complex {K : CochainComplex 𝒜 ℤ} (I : InjectiveResolution K) :
    CochainComplex 𝒜 ℤ :=
  Plus.TermsIn.QuasiIsoTo.complex I

/-- The resolving complex in an injective resolution is K-injective. -/
@[stacks 013R "injective resolutions are K-injective"]
instance instIsKInjective {K : CochainComplex 𝒜 ℤ} (I : InjectiveResolution K) :
    IsKInjective I.complex :=
  Plus.TermsIn.instIsKInjective I.model

/-- Forgetting the bundled injective model gives the resolving cochain complex. -/
theorem model_coe {K : CochainComplex 𝒜 ℤ} (I : InjectiveResolution K) :
    (I.model : CochainComplex 𝒜 ℤ) = I.complex := sorry

/-- The comparison map from the original complex to its injective model. -/
abbrev ι {K : CochainComplex 𝒜 ℤ} (I : InjectiveResolution K) :
    K ⟶ I.complex :=
  Plus.TermsIn.QuasiIsoTo.comparison I

/-- The comparison map of an injective resolution is a quasi-isomorphism. -/
theorem quasiIso {K : CochainComplex 𝒜 ℤ} (I : InjectiveResolution K) :
    QuasiIso I.ι := sorry

attribute [instance] InjectiveResolution.quasiIso

/-- The morphism of bounded-below injective models underlying a resolution morphism. -/
abbrev modelHom {K : CochainComplex 𝒜 ℤ} {I J : InjectiveResolution K} (f : I ⟶ J) :
    I.model ⟶ J.model :=
  Plus.TermsIn.QuasiIsoTo.modelHom f

/-- Morphisms of injective resolutions are determined by their morphisms of bundled models. -/
@[ext]
theorem hom_ext {K : CochainComplex 𝒜 ℤ} {I J : InjectiveResolution K}
    {f g : I ⟶ J} (h : modelHom f = modelHom g) : f = g := sorry

/-- The cochain map underlying a morphism of injective resolutions. -/
abbrev hom {K : CochainComplex 𝒜 ℤ} {I J : InjectiveResolution K} (f : I ⟶ J) :
    I.complex ⟶ J.complex :=
  Plus.TermsIn.QuasiIsoTo.hom f

/-- The cochain map of a resolution morphism is induced by its injective-model morphism. -/
@[simp]
theorem hom_eq_map_modelHom {K : CochainComplex 𝒜 ℤ}
    {I J : InjectiveResolution K} (f : I ⟶ J) :
    hom f = (InjectivePlus.ι 𝒜).map (modelHom f) := sorry

/-- The identity resolution morphism induces the identity injective-model morphism. -/
@[simp]
theorem id_modelHom {K : CochainComplex 𝒜 ℤ} (I : InjectiveResolution K) :
    modelHom (𝟙 I) = 𝟙 I.model := sorry

/-- Composition of resolution morphisms induces composition of injective-model morphisms. -/
@[simp]
theorem comp_modelHom {K : CochainComplex 𝒜 ℤ} {I J H : InjectiveResolution K}
    (f : I ⟶ J) (g : J ⟶ H) :
    modelHom (f ≫ g) = modelHom f ≫ modelHom g := sorry

/-- The identity resolution morphism induces the identity cochain map. -/
@[simp]
theorem id_hom {K : CochainComplex 𝒜 ℤ} (I : InjectiveResolution K) :
    hom (𝟙 I) = 𝟙 I.complex := sorry

/-- Composition of resolution morphisms induces composition of cochain maps. -/
@[simp]
theorem comp_hom {K : CochainComplex 𝒜 ℤ} {I J H : InjectiveResolution K}
    (f : I ⟶ J) (g : J ⟶ H) :
    hom (f ≫ g) = hom f ≫ hom g := sorry

/-- A morphism of injective resolutions commutes with the comparison maps. -/
@[reassoc]
theorem ι_naturality {K : CochainComplex 𝒜 ℤ} {I J : InjectiveResolution K} (f : I ⟶ J) :
    I.ι ≫ hom f = J.ι := sorry

/-- The functor selecting the bounded-below injective model of a resolution. -/
abbrev modelFunctor (K : CochainComplex 𝒜 ℤ) :
    InjectiveResolution K ⥤ InjectivePlus 𝒜 :=
  Plus.TermsIn.QuasiIsoTo.modelFunctor (isInjective 𝒜) K

/-- The injective-model functor returns the bundled model of a resolution. -/
@[simp]
theorem modelFunctor_obj {K : CochainComplex 𝒜 ℤ} (I : InjectiveResolution K) :
    (modelFunctor K).obj I = I.model := sorry

/-- The injective-model functor returns the model morphism of a resolution morphism. -/
@[simp]
theorem modelFunctor_map {K : CochainComplex 𝒜 ℤ}
    {I J : InjectiveResolution K} (f : I ⟶ J) :
    (modelFunctor K).map f = modelHom f := sorry

/-- The functor selecting the underlying cochain complex of an injective resolution. -/
abbrev complexFunctor (K : CochainComplex 𝒜 ℤ) :
    InjectiveResolution K ⥤ CochainComplex 𝒜 ℤ :=
  Plus.TermsIn.QuasiIsoTo.complexFunctor (isInjective 𝒜) K

/-- The underlying-complex functor returns the resolving complex. -/
@[simp]
theorem complexFunctor_obj {K : CochainComplex 𝒜 ℤ} (I : InjectiveResolution K) :
    (complexFunctor K).obj I = I.complex := sorry

/-- The underlying-complex functor returns the cochain map of a resolution morphism. -/
@[simp]
theorem complexFunctor_map {K : CochainComplex 𝒜 ℤ}
    {I J : InjectiveResolution K} (f : I ⟶ J) :
    (complexFunctor K).map f = hom f := sorry

/-- Forgetting the bundled injective models identifies the model and complex functors. -/
theorem modelFunctor_comp_ι (K : CochainComplex 𝒜 ℤ) :
    modelFunctor K ⋙ InjectivePlus.ι 𝒜 = complexFunctor K := sorry

/-- The injective-resolution comparisons form a natural transformation. -/
abbrev ιNatTrans (K : CochainComplex 𝒜 ℤ) :
    (Functor.const (InjectiveResolution K)).obj K ⟶ complexFunctor K :=
  Plus.TermsIn.QuasiIsoTo.comparisonNatTrans (isInjective 𝒜) K

/-- Evaluating the injective-resolution comparison transformation gives its comparison map. -/
@[simp]
theorem ιNatTrans_app {K : CochainComplex 𝒜 ℤ} (I : InjectiveResolution K) :
    (ιNatTrans K).app I = I.ι := sorry

/-- The named constructor retains the supplied bundled injective model. -/
@[simp]
theorem mk_model {K : CochainComplex 𝒜 ℤ} (I : InjectivePlus 𝒜)
    (f : K ⟶ (I : CochainComplex 𝒜 ℤ)) (hf : QuasiIso f) :
    (mk I f hf).model = I := sorry

/-- The named constructor retains the underlying complex of the supplied model. -/
@[simp]
theorem mk_complex {K : CochainComplex 𝒜 ℤ} (I : InjectivePlus 𝒜)
    (f : K ⟶ (I : CochainComplex 𝒜 ℤ)) (hf : QuasiIso f) :
    (mk I f hf).complex = (I : CochainComplex 𝒜 ℤ) := sorry

/-- The named constructor retains the supplied comparison map. -/
@[simp]
theorem mk_ι {K : CochainComplex 𝒜 ℤ} (I : InjectivePlus 𝒜)
    (f : K ⟶ (I : CochainComplex 𝒜 ℤ)) (hf : QuasiIso f) :
    (mk I f hf).ι = f := sorry

/-- Injective resolutions exist exactly when explicit bounded-below injective comparison data
exist. -/
theorem nonempty_iff {K : CochainComplex 𝒜 ℤ} :
    Nonempty (InjectiveResolution K) ↔
      ∃ (I : InjectivePlus 𝒜) (f : K ⟶ (I : CochainComplex 𝒜 ℤ)), QuasiIso f := sorry

end InjectiveResolution

namespace Plus.TermsIn.Bounded.QuasiIso

variable {a : ℤ} {K I : CochainComplex 𝒜 ℤ} {α : K ⟶ I}

/-- Package a bounded-below quasi-isomorphism into a termwise-injective complex
as a cochain-complex injective resolution. -/
@[stacks 013I]
abbrev toInjectiveResolution
    (h : Plus.TermsIn.Bounded.QuasiIso (isInjective 𝒜) a K I α) :
    InjectiveResolution K :=
  InjectiveResolution.mk h.toPlus α h.quasiIso

end Plus.TermsIn.Bounded.QuasiIso

namespace Plus.TermsIn.Bounded.QuasiIso.Mono

variable {a : ℤ} {K I : CochainComplex 𝒜 ℤ} {α : K ⟶ I}

/-- Package a termwise-monomorphic bounded-below quasi-isomorphism into a
termwise-injective complex as a cochain-complex injective resolution. -/
@[stacks 013I]
abbrev toInjectiveResolution
    (h : Plus.TermsIn.Bounded.QuasiIso.Mono (isInjective 𝒜) a K I α) :
    InjectiveResolution K :=
  h.toQuasiIso.toInjectiveResolution

end Plus.TermsIn.Bounded.QuasiIso.Mono

namespace InjectiveResolution

/-- The resolving complex is bounded below. -/
theorem plus {K : CochainComplex 𝒜 ℤ} (I : InjectiveResolution K) :
    CochainComplex.plus 𝒜 I.complex := by
  simpa using I.model.plus

/-- The resolving complex is zero in sufficiently negative degrees. -/
theorem exists_isStrictlyGE {K : CochainComplex 𝒜 ℤ} (I : InjectiveResolution K) :
    ∃ a : ℤ, I.complex.IsStrictlyGE a := by
  simpa using I.model.exists_bound

/-- Each term of the resolving complex is injective. -/
theorem injective {K : CochainComplex 𝒜 ℤ} (I : InjectiveResolution K) (n : ℤ) :
    Injective (I.complex.X n) := by
  simpa using I.model.term_mem n

attribute [instance] InjectiveResolution.injective

/-- Stacks 013J: a cochain complex admitting a bounded-below injective
resolution has zero homology in all sufficiently negative degrees. -/
@[stacks 013J]
theorem eventually_isZero_homology {K : CochainComplex 𝒜 ℤ}
    (I : InjectiveResolution K) :
    ∃ a : ℤ, ∀ n : ℤ, n < a → IsZero (K.homology n) := sorry

/-- Stacks 013K (2): a cochain complex with homology zero in sufficiently
negative degrees admits a bounded-below injective resolution. -/
@[stacks 013K]
theorem nonempty_of_eventually_isZero_homology [EnoughInjectives 𝒜]
    {K : CochainComplex 𝒜 ℤ}
    (hK : ∃ a : ℤ, ∀ n : ℤ, n < a → IsZero (K.homology n)) :
    Nonempty (InjectiveResolution K) := sorry

/-- Stacks 013K (3): a cochain complex zero below `a` admits an injective
resolution whose target is zero below `a` and whose comparison is termwise
monomorphic. -/
@[stacks 013K]
theorem exists_strictlyGE_with_termwise_mono [EnoughInjectives 𝒜]
    {K : CochainComplex 𝒜 ℤ}
    (a : ℤ) (hK : K.IsStrictlyGE a) :
    ∃ I : InjectiveResolution K,
      I.complex.IsStrictlyGE a ∧ ∀ n : ℤ, Mono (I.ι.f n) := sorry

end InjectiveResolution

end CochainComplex


