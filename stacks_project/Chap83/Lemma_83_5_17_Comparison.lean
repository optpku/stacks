/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import Mathlib.CategoryTheory.Limits.Constructions.Over.Basic
public import stacks_project.Chap83.Definition_83_4_1_Invariant

/-!
# Comparison square of a pre-relation and a morphism

This module names the comparison morphism `c : U ×_X U ⟶ U ×_B U` of a slice morphism
`φ : U ⟶ X`, the projections `p` and `q` of its pullback along a pre-relation, and the
induced morphism `R ⟶ U ×_X U` when `φ` is `R`-invariant.
-/

@[expose] public section

open CategoryTheory AlgebraicGeometry AlgebraicSpace Limits

noncomputable section

universe u

namespace AlgebraicGeometry.AlgebraicSpace.PreRelation

/-- The comparison `c : pullback φ φ ⟶ U ⨯ U` sending a pair in `U ×_X U` to the same
pair in `U ×_B U`. -/
def comparison {S : Scheme.{u}} {B : AlgebraicSpace S} {U X : Over B} (φ : U ⟶ X) :
    pullback φ φ ⟶ U ⨯ U :=
  prod.lift (pullback.fst φ φ) (pullback.snd φ φ)

/-- The first projection of `comparison φ` is `pullback.fst φ φ`. -/
theorem comparison_fst {S : Scheme.{u}} {B : AlgebraicSpace S} {U X : Over B}
    (φ : U ⟶ X) :
    comparison φ ≫ prod.fst = pullback.fst φ φ :=
  sorry

/-- The second projection of `comparison φ` is `pullback.snd φ φ`. -/
theorem comparison_snd {S : Scheme.{u}} {B : AlgebraicSpace S} {U X : Over B}
    (φ : U ⟶ X) :
    comparison φ ≫ prod.snd = pullback.snd φ φ :=
  sorry

/-- The comparison morphism is the product lift of the two kernel-pair projections. -/
theorem comparison_spec {S : Scheme.{u}} {B : AlgebraicSpace S} {U X : Over B}
    (φ : U ⟶ X) :
    comparison φ ≫ prod.fst = pullback.fst φ φ ∧
      comparison φ ≫ prod.snd = pullback.snd φ φ :=
  sorry

/-- The projection `p` of the pullback of `comparison φ` along `P.hom`, landing in the
source of the pre-relation. -/
def toRelation {S : Scheme.{u}} {B : AlgebraicSpace S} {U X : Over B}
    (P : PreRelation U) (φ : U ⟶ X) :
    pullback (comparison φ) P.hom ⟶ P.left :=
  pullback.snd (comparison φ) P.hom

/-- `P.toRelation φ` is the second projection of the pullback of `comparison φ` along
`P.hom`. -/
theorem toRelation_spec {S : Scheme.{u}} {B : AlgebraicSpace S} {U X : Over B}
    (P : PreRelation U) (φ : U ⟶ X) :
    P.toRelation φ = pullback.snd (comparison φ) P.hom :=
  sorry

/-- The projection `q` of the pullback of `comparison φ` along `P.hom`, landing in the
kernel pair `U ×_X U`. -/
def toKernelPair {S : Scheme.{u}} {B : AlgebraicSpace S} {U X : Over B}
    (P : PreRelation U) (φ : U ⟶ X) :
    pullback (comparison φ) P.hom ⟶ pullback φ φ :=
  pullback.fst (comparison φ) P.hom

/-- `P.toKernelPair φ` is the first projection of the pullback of `comparison φ` along
`P.hom`. -/
theorem toKernelPair_spec {S : Scheme.{u}} {B : AlgebraicSpace S} {U X : Over B}
    (P : PreRelation U) (φ : U ⟶ X) :
    P.toKernelPair φ = pullback.fst (comparison φ) P.hom :=
  sorry

/-- The square with vertices `pullback (comparison φ) P.hom`, `P.left`, `pullback φ φ`,
and `U ⨯ U` commutes. -/
theorem toKernelPair_comp_comparison {S : Scheme.{u}} {B : AlgebraicSpace S}
    {U X : Over B} (P : PreRelation U) (φ : U ⟶ X) :
    P.toKernelPair φ ≫ comparison φ = P.toRelation φ ≫ P.hom :=
  sorry

/-- The induced morphism `R ⟶ U ×_X U` associated to an `R`-invariant morphism `φ`. -/
def induced {S : Scheme.{u}} {B : AlgebraicSpace S} {U X : Over B}
    (P : PreRelation U) {φ : U ⟶ X} (hφ : P.IsInvariant φ) :
    P.left ⟶ pullback φ φ :=
  pullback.lift P.t P.s hφ

/-- The first projection of `P.induced hφ` is the target map of the pre-relation. -/
theorem induced_fst {S : Scheme.{u}} {B : AlgebraicSpace S} {U X : Over B}
    (P : PreRelation U) {φ : U ⟶ X} (hφ : P.IsInvariant φ) :
    P.induced hφ ≫ pullback.fst φ φ = P.t :=
  sorry

/-- The second projection of `P.induced hφ` is the source map of the pre-relation. -/
theorem induced_snd {S : Scheme.{u}} {B : AlgebraicSpace S} {U X : Over B}
    (P : PreRelation U) {φ : U ⟶ X} (hφ : P.IsInvariant φ) :
    P.induced hφ ≫ pullback.snd φ φ = P.s :=
  sorry

/-- The induced morphism composes with `comparison φ` to the defining map of `P`. -/
theorem induced_comp {S : Scheme.{u}} {B : AlgebraicSpace S} {U X : Over B}
    (P : PreRelation U) {φ : U ⟶ X} (hφ : P.IsInvariant φ) :
    P.induced hφ ≫ comparison φ = P.hom :=
  sorry

end AlgebraicGeometry.AlgebraicSpace.PreRelation
