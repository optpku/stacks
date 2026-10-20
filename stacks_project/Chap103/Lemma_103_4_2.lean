/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import stacks_project.Chap94.Definition_94_12_1_AlgebraicStack
public import stacks_project.Chap100.Definition_100_5_1_Surjective
public import stacks_project.Chap101.Lemma_101_25_5_Flat
public import stacks_project.Chap103.Lemma_103_4_2_Restriction

/-!
# Detection of monomorphisms, epimorphisms, and isomorphisms in QCoh

On an algebraic stack, a morphism of quasi-coherent modules is a monomorphism,
epimorphism, or isomorphism if and only if each small-étale restriction along
a jointly surjective family of flat objects is so.
-/

@[expose] public section

open AlgebraicGeometry CategoryTheory
open AlgebraicGeometry.AlgebraicStack AlgebraicGeometry.GroupoidsOver
open scoped Bicategory

noncomputable section

universe u v

namespace AlgebraicGeometry.AlgebraicStack

variable {S : Scheme.{u}} {X : GroupoidsOver S} [AlgebraicStack X]

/-- A family of objects `x i : U i ⟶ X` is jointly surjective when
`∐ x i : ∐ U i ⟶ X` is surjective on points of algebraic stacks. -/
def jointlySurjective {I : Type v} {U : I → Over S}
    (x : ∀ i, GroupoidsOver.slice (U i) ⟶ X) : Prop :=
  Function.Surjective
    (fun p : (i : I) × Points (GroupoidsOver.slice (U i)) ↦ Points.map (x p.1) p.2)

/-- Joint surjectivity of a family of objects is equivalent to every point of
`X` lying in the image of some `Points.map (x i)`. -/
theorem jointlySurjective_iff {I : Type v} {U : I → Over S}
    (x : ∀ i, GroupoidsOver.slice (U i) ⟶ X) :
    jointlySurjective x ↔ ∀ y : Points X, ∃ i, y ∈ Set.range (Points.map (x i)) :=
  sorry

/-- Lemma 103.4.2 (1): let `X` be an algebraic stack. Let `I` be a set and for
`i : I` let `x i : U i ⟶ X` be an object of `X`. Assume that `x i` is flat and
`∐ x i : ∐ U i ⟶ X` is surjective. Let `φ : F ⟶ G` be an arrow of `QCoh X`.
Then `φ` is a monomorphism if and only if each restriction of `φ` to
`(U i)_étale` is a monomorphism. -/
@[stacks 0GQF]
theorem mono_iff_forall_restrict {I : Type v} {U : I → Over S}
    {x : ∀ i, GroupoidsOver.slice (U i) ⟶ X} [∀ i, Flat (x i)]
    (h_surj : jointlySurjective x) {F G : QCoh X} (φ : F ⟶ G) :
    Mono φ ↔ ∀ i, Mono ((QCoh.restrictToSmallEtale X (objectOfHom (x i))).map φ) :=
  sorry

/-- Lemma 103.4.2 (2): let `X` be an algebraic stack. Let `I` be a set and for
`i : I` let `x i : U i ⟶ X` be an object of `X`. Assume that `x i` is flat and
`∐ x i : ∐ U i ⟶ X` is surjective. Let `φ : F ⟶ G` be an arrow of `QCoh X`.
Then `φ` is an epimorphism if and only if each restriction of `φ` to
`(U i)_étale` is an epimorphism. -/
@[stacks 0GQF]
theorem epi_iff_forall_restrict {I : Type v} {U : I → Over S}
    {x : ∀ i, GroupoidsOver.slice (U i) ⟶ X} [∀ i, Flat (x i)]
    (h_surj : jointlySurjective x) {F G : QCoh X} (φ : F ⟶ G) :
    Epi φ ↔ ∀ i, Epi ((QCoh.restrictToSmallEtale X (objectOfHom (x i))).map φ) :=
  sorry

/-- Lemma 103.4.2 (3): let `X` be an algebraic stack. Let `I` be a set and for
`i : I` let `x i : U i ⟶ X` be an object of `X`. Assume that `x i` is flat and
`∐ x i : ∐ U i ⟶ X` is surjective. Let `φ : F ⟶ G` be an arrow of `QCoh X`.
Then `φ` is an isomorphism if and only if each restriction of `φ` to
`(U i)_étale` is an isomorphism. -/
@[stacks 0GQF]
theorem isIso_iff_forall_restrict {I : Type v} {U : I → Over S}
    {x : ∀ i, GroupoidsOver.slice (U i) ⟶ X} [∀ i, Flat (x i)]
    (h_surj : jointlySurjective x) {F G : QCoh X} (φ : F ⟶ G) :
    IsIso φ ↔ ∀ i, IsIso ((QCoh.restrictToSmallEtale X (objectOfHom (x i))).map φ) :=
  sorry

end AlgebraicGeometry.AlgebraicStack
