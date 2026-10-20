/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import Mathlib.CategoryTheory.Limits.Constructions.Over.Basic
public import ReasLib.AlgebraicGeometry.AlgebraicSpace.PreRelation.CategoricalQuotient
public import ReasLib.CategoryTheory.Limits.Shapes.Cofork.BaseChange

/-!
# Base change of pre-relations

This module records the base change of an invariant pre-relation along a morphism of
targets.
-/

@[expose] public section

open CategoryTheory AlgebraicGeometry AlgebraicSpace Limits

noncomputable section

universe u

namespace AlgebraicGeometry.AlgebraicSpace
namespace PreRelation

/-- The base change of an invariant morphism `φ : U ⟶ X` along `f : X' ⟶ X` is the
pre-relation `j'` on `pullback φ f` whose projections are the base-changed parallel arrows
of the cofork associated to `φ`. -/
def baseChange {S : Scheme.{u}} {B : AlgebraicSpace S} {U X X' : Over B}
    (P : PreRelation U) {φ : U ⟶ X} (hφ : P.IsInvariantHom φ) (f : X' ⟶ X) :
    PreRelation (pullback φ f) :=
  ofHom (prod.lift
    ((P.cofork hφ).baseChangeLeft f)
    ((P.cofork hφ).baseChangeRight f))

/-- The first projection of a base-changed pre-relation is the left base-changed parallel arrow. -/
theorem baseChange_t {S : Scheme.{u}} {B : AlgebraicSpace S} {U X X' : Over B}
    (P : PreRelation U) {φ : U ⟶ X} (hφ : P.IsInvariantHom φ) (f : X' ⟶ X) :
    (P.baseChange hφ f).t = (P.cofork hφ).baseChangeLeft f := sorry

/-- The second projection of a base-changed pre-relation is the right base-changed parallel arrow. -/
theorem baseChange_s {S : Scheme.{u}} {B : AlgebraicSpace S} {U X X' : Over B}
    (P : PreRelation U) {φ : U ⟶ X} (hφ : P.IsInvariantHom φ) (f : X' ⟶ X) :
    (P.baseChange hφ f).s = (P.cofork hφ).baseChangeRight f := sorry

/-- The defining map of a base-changed pre-relation is the product lift of its parallel arrows. -/
theorem baseChange_hom {S : Scheme.{u}} {B : AlgebraicSpace S} {U X X' : Over B}
    (P : PreRelation U) {φ : U ⟶ X} (hφ : P.IsInvariantHom φ) (f : X' ⟶ X) :
    (P.baseChange hφ f).hom =
      prod.lift
        ((P.cofork hφ).baseChangeLeft f)
        ((P.cofork hφ).baseChangeRight f) := sorry

/-- The arrow space of a base-changed pre-relation is the pullback of the original
relation arrow space along the target morphism. -/
theorem baseChange_left {S : Scheme.{u}} {B : AlgebraicSpace S} {U X X' : Over B}
    (P : PreRelation U) {φ : U ⟶ X} (hφ : P.IsInvariantHom φ) (f : X' ⟶ X) :
    (P.baseChange hφ f).left = pullback (P.t ≫ φ) f := sorry

/-- Base change preserves the monomorphism condition on the defining map of a relation. -/
theorem monoHom_baseChange {S : Scheme.{u}} {B : AlgebraicSpace S}
    {U X X' : Over B} (P : PreRelation U) {φ : U ⟶ X} (hφ : P.IsInvariantHom φ)
    (f : X' ⟶ X) [Mono P.hom] : Mono (P.baseChange hφ f).hom := sorry

namespace IsPreEquivalence

/-- Base change preserves pointwise pre-equivalence of a pre-relation. -/
theorem baseChange {S : Scheme.{u}} {B : AlgebraicSpace S} {U X X' : Over B}
    {P : PreRelation U} (hP : P.IsPreEquivalence) {φ : U ⟶ X}
    (hφ : P.IsInvariantHom φ) (f : X' ⟶ X) :
    (P.baseChange hφ f).IsPreEquivalence := sorry

end IsPreEquivalence

/-- Base change preserves the equivalence-relation condition on the projections. -/
theorem isEquivalenceRelation_baseChange {S : Scheme.{u}} {B : AlgebraicSpace S}
    {U X X' : Over B} (P : PreRelation U) {φ : U ⟶ X} (hφ : P.IsInvariantHom φ)
    (f : X' ⟶ X) [IsEquivalenceRelation P.t P.s] :
    IsEquivalenceRelation (P.baseChange hφ f).t (P.baseChange hφ f).s := sorry

end PreRelation
end AlgebraicGeometry.AlgebraicSpace
