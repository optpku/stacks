/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.Geometry.Manifold.Complex.CompactRiemannSurface
public import ReasLib.Geometry.Manifold.Complex.MeromorphicFunctionField
public import ReasLib.Geometry.Manifold.Complex.MeromorphicFunctionField.Pullback
public import ReasLib.FieldTheory.Extension.Category
public import ReasLib.FieldTheory.Transcendence.OneVariable
public import Mathlib.CategoryTheory.Equivalence

@[expose] public section

/-!
# Function Fields of Compact Riemann Surfaces

This module connects the meromorphic function field of a compact Riemann surface to the generic
transcendence-degree-one API in `FieldExtension`.
-/

open scoped IntermediateField Manifold MeromorphicFunctionField
open IntermediateField
open IntermediateField.AdjoinSimple
open CategoryTheory Opposite

universe u

namespace CompactRiemannSurface

/-- The meromorphic function field of a compact Riemann surface has transcendence degree one over
`ℂ`. -/
theorem functionField_trdeg_eq_one (X : CompactRiemannSurface.{u}) :
    Algebra.trdeg ℂ (ℂ(X)) = 1 := sorry

/-- The meromorphic function field of a compact Riemann surface is finitely generated as a
field extension of `ℂ`. It is essentially finite type as an algebra, rather than finite type. -/
instance functionField_essFiniteType (X : CompactRiemannSurface.{u}) :
    Algebra.EssFiniteType ℂ (ℂ(X)) := sorry

/-- The contravariant function-field functor sends a nonconstant holomorphic map to pullback
of meromorphic functions. -/
noncomputable def functionFieldFunctor : CompactRiemannSurface.Nonconstant.{u} ⥤
    (AlgebraicGeometry.FinitelyGeneratedFieldExtension.TranscendenceDegreeOne.{0, u} ℂ)ᵒᵖ where
  obj X := op <| AlgebraicGeometry.FinitelyGeneratedFieldExtension.TranscendenceDegreeOne.of ℂ
    ℂ(X.obj) (functionField_trdeg_eq_one X.obj)
  map {X Y} f :=
    (ObjectProperty.homMk <| ObjectProperty.homMk <| CommAlgCat.ofHom <|
      MeromorphicFunctionField.pullback (X := X.obj) (Y := Y.obj) f.hom f.property).op
  map_id X := sorry
  map_comp f g := sorry

/-- The underlying complex algebra of the functor's object is the meromorphic function field. -/
@[simp]
theorem functionFieldFunctor_obj (X : CompactRiemannSurface.Nonconstant.{u}) :
    (functionFieldFunctor.obj X).unop.obj.obj = CommAlgCat.of ℂ ℂ(X.obj) := rfl

/-- The algebra map underlying the functor's image of a morphism is meromorphic pullback. -/
@[simp]
theorem functionFieldFunctor_map {X Y : CompactRiemannSurface.Nonconstant.{u}} (f : X ⟶ Y) :
    (functionFieldFunctor.map f).unop.hom.hom.hom =
      MeromorphicFunctionField.pullback (X := X.obj) (Y := Y.obj) f.hom f.property := rfl

/-- Every complex-algebra map between function fields is pullback by a nonconstant
holomorphic map. -/
instance functionFieldFunctor_full : functionFieldFunctor.{u}.Full := sorry

/-- Nonconstant holomorphic maps are determined by pullback on meromorphic functions. -/
instance functionFieldFunctor_faithful : functionFieldFunctor.{u}.Faithful := sorry

/-- Every finitely generated complex field extension of transcendence degree one is in the
essential image of the function-field functor. -/
instance functionFieldFunctor_essSurj : functionFieldFunctor.{u}.EssSurj := sorry

/-- Compact Riemann surfaces with nonconstant holomorphic maps are anti-equivalent to
finitely generated complex field extensions of transcendence degree one. -/
instance functionFieldFunctor_isEquivalence : functionFieldFunctor.{u}.IsEquivalence where
  full := functionFieldFunctor_full
  faithful := functionFieldFunctor_faithful
  essSurj := functionFieldFunctor_essSurj

/-- Every essentially finite type extension of `ℂ` of transcendence degree one is realized as the
meromorphic function field of a compact Riemann surface. -/
theorem existsWithFunctionFieldOfEssFiniteTypeTrdegEqOne
    (K : Type u) [Field K] [Algebra ℂ K] [Algebra.EssFiniteType ℂ K]
    (htrdeg : Algebra.trdeg ℂ K = 1) :
    ∃ X : CompactRiemannSurface.{u}, Nonempty (K ≃ₐ[ℂ] ℂ(X)) := sorry

/-- Isomorphism of compact Riemann surfaces is detected contravariantly by their meromorphic
function fields. -/
theorem nonemptyIsoIffNonemptyFunctionFieldAlgEquiv
    (X Y : CompactRiemannSurface.{u}) :
    Nonempty (X ≅ Y) ↔ Nonempty (ℂ(Y) ≃ₐ[ℂ] ℂ(X)) := sorry

namespace FunctionField

/-- A nonconstant meromorphic function on a compact Riemann surface is transcendental over
`ℂ`. -/
theorem transcendentalOfNotMemRange
    {X : CompactRiemannSurface.{u}} {f : ℂ(X)}
    (hf : f ∉ Set.range (algebraMap ℂ (ℂ(X)))) :
    Transcendental ℂ f := by
  change ¬ IsAlgebraic ℂ f
  intro hf_alg
  have hbot : (ℂ⟮f⟯ : IntermediateField ℂ (ℂ(X))) = ⊥ := by
    -- Local instance justification (proof-local temporary data): the algebraic simple extension
    -- is used with the algebraically closed constant field only in this contradiction.
    letI : Algebra.IsAlgebraic ℂ ℂ⟮f⟯ := isAlgebraic_adjoin_simple hf_alg.isIntegral
    simpa using eq_bot_of_isAlgClosed_of_isAlgebraic (ℂ⟮f⟯ : IntermediateField ℂ (ℂ(X)))
  exact hf <| mem_bot.mp <| adjoin_simple_eq_bot_iff.mp hbot

/-- A degree-one function field has a nonconstant meromorphic generator over which it is
algebraic. -/
lemma existsGeneratorOfTrdegEqOne
    {X : CompactRiemannSurface.{u}} (htrdeg : Algebra.trdeg ℂ (ℂ(X)) = 1) :
    ∃ f : ℂ(X), f ∉ Set.range (algebraMap ℂ (ℂ(X))) ∧
      Algebra.IsAlgebraic ℂ⟮f⟯ (ℂ(X)) := by
  obtain ⟨f, hf_nonconst⟩ :=
    FieldExtension.existsNotMemRangeAlgebraMapOfTrdegEqOne htrdeg
  exact ⟨f, hf_nonconst,
    FieldExtension.isAlgebraicAdjoinSimpleOfTranscendentalOfTrdegEqOne
      (transcendentalOfNotMemRange hf_nonconst) htrdeg⟩

/-- Every compact Riemann surface has a nonconstant meromorphic generator over which its
function field is algebraic. -/
theorem existsGenerator (X : CompactRiemannSurface.{u}) :
    ∃ f : ℂ(X), f ∉ Set.range (algebraMap ℂ (ℂ(X))) ∧
      Algebra.IsAlgebraic ℂ⟮f⟯ (ℂ(X)) := by
  exact existsGeneratorOfTrdegEqOne
    (CompactRiemannSurface.functionField_trdeg_eq_one X)

/-- A nonconstant meromorphic generator algebraically cofinal in a function field forces that
function field to have transcendence degree one. -/
lemma trdegEqOneOfExistsGenerator
    {X : CompactRiemannSurface.{u}}
    (hgen : ∃ f : ℂ(X), f ∉ Set.range (algebraMap ℂ (ℂ(X))) ∧
      Algebra.IsAlgebraic ℂ⟮f⟯ (ℂ(X))) :
    Algebra.trdeg ℂ (ℂ(X)) = 1 := by
  obtain ⟨f, hf_nonconst, hf_alg⟩ := hgen
  have hf_trans : Transcendental ℂ f :=
    transcendentalOfNotMemRange hf_nonconst
  simpa using
    FieldExtension.trdegEqOneOfTranscendentalIsAlgebraicOverAdjoinSimple
      (K := ℂ(X)) hf_trans hf_alg

/-- A nonconstant meromorphic function on a compact Riemann surface generates an algebraically
cofinal simple subfield of its function field. -/
theorem isAlgebraicOverAdjoinOfNonconstant
    (X : CompactRiemannSurface.{u}) (f : ℂ(X))
    (hf : f ∉ Set.range (algebraMap ℂ (ℂ(X)))) :
    Algebra.IsAlgebraic ℂ⟮f⟯ (ℂ(X)) := by
  exact FieldExtension.isAlgebraicAdjoinSimpleOfTranscendentalOfTrdegEqOne
    (transcendentalOfNotMemRange hf)
    (CompactRiemannSurface.functionField_trdeg_eq_one X)

end FunctionField

end CompactRiemannSurface
