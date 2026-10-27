/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.AlgebraicGeometry.AlgebraicStack.JointlySurjective
public import ReasLib.AlgebraicGeometry.GroupoidsOver.Module.Quasicoherent.SmallEtale
public import ReasLib.AlgebraicGeometry.AlgebraicStack.Flat
public import ReasLib.AlgebraicGeometry.GroupoidsOver.Yoneda

/-!
# Detection of morphism properties along flat covers
-/

@[expose] public section

open AlgebraicGeometry CategoryTheory
open AlgebraicGeometry.AlgebraicStack AlgebraicGeometry.GroupoidsOver
open scoped Bicategory

noncomputable section

universe u v

namespace AlgebraicGeometry.AlgebraicStack

variable {S : Scheme.{u}} {X : GroupoidsOver S} [AlgebraicStack X]

/-- A morphism of quasi-coherent modules on an algebraic stack is a monomorphism
if and only if its small-étale restriction along each object of a jointly
surjective family of flat objects is a monomorphism. -/
theorem mono_iff_forall_restrict {I : Type v} {U : I → Over S}
    {x : ∀ i, GroupoidsOver.slice (U i) ⟶ X} [∀ i, Flat (x i)]
    (h_surj : jointlySurjective x) {F G : QCoh X} (φ : F ⟶ G) :
    Mono φ ↔ ∀ i, Mono ((QCoh.restrictToSmallEtale X (evalId (x i))).map φ) := sorry

/-- A morphism of quasi-coherent modules on an algebraic stack is an epimorphism
if and only if its small-étale restriction along each object of a jointly
surjective family of flat objects is an epimorphism. -/
theorem epi_iff_forall_restrict {I : Type v} {U : I → Over S}
    {x : ∀ i, GroupoidsOver.slice (U i) ⟶ X} [∀ i, Flat (x i)]
    (h_surj : jointlySurjective x) {F G : QCoh X} (φ : F ⟶ G) :
    Epi φ ↔ ∀ i, Epi ((QCoh.restrictToSmallEtale X (evalId (x i))).map φ) := sorry

/-- A morphism of quasi-coherent modules on an algebraic stack is an isomorphism
if and only if its small-étale restriction along each object of a jointly
surjective family of flat objects is an isomorphism. -/
theorem isIso_iff_forall_restrict {I : Type v} {U : I → Over S}
    {x : ∀ i, GroupoidsOver.slice (U i) ⟶ X} [∀ i, Flat (x i)]
    (h_surj : jointlySurjective x) {F G : QCoh X} (φ : F ⟶ G) :
    IsIso φ ↔ ∀ i, IsIso ((QCoh.restrictToSmallEtale X (evalId (x i))).map φ) := sorry

end AlgebraicGeometry.AlgebraicStack
