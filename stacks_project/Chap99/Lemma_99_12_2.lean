/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import Mathlib.AlgebraicGeometry.OpenImmersion
public import Mathlib.CategoryTheory.MorphismProperty.Representable
public import Mathlib.CategoryTheory.Yoneda
public import stacks_project.Chap99.Lemma_99_12_1_Graph
public import stacks_project.Chap99.Lemma_99_12_2_Projection

/-!
# Lemma 99.12.2

Under the standing hypotheses of Lemma 99.12.1, the graph transformation
`Mor_B(Z, X) ⟶ Hilb_{Z ×_B X / B}` is representable by open immersions.
-/

@[expose] public section

open CategoryTheory AlgebraicGeometry AlgebraicGeometry.AlgebraicSpace
open AlgebraicGeometry.AlgebraicSpace.Quot (SchemesOver)
open AlgebraicGeometry.AlgebraicSpace.RelativeHom

noncomputable section

universe u

namespace AlgebraicGeometry.AlgebraicSpace.RelativeHom

variable {S : Scheme.{u}} {Z B X : AlgebraicSpace S}

/-- Open immersions of the underlying scheme morphisms, as a morphism property
on schemes over an algebraic space `B`. -/
abbrev openImmersion : MorphismProperty (SchemesOver B) :=
  fun _ _ h ↦ AlgebraicGeometry.IsOpenImmersion h.left.left

/-- Lemma 99.12.2: assumption and notation as in Lemma 99.12.1. The graph
transformation `graph z x : mor z x ⟶ hilb z x` from `Mor_B(Z, X)` to
`Hilb_{Z ×_B X / B}` is representable by open immersions. -/
@[stacks 0D1B]
theorem graph_isOpenImmersion (z : Z ⟶ B) (x : X ⟶ B) [Separated x]
    [FinitePresentation z] [Flat z] [Proper z] :
    openImmersion.relative uliftYoneda.{u + 1} (graph z x) :=
  sorry

/-- For a Hilbert point `Y ⊂ (Z ×_B X)_T` there is an open `V ⊂ T` such that a
morphism of schemes `T' ⟶ T` factors through `V` if and only if the
base-changed first projection `pr₁|_Y` is an isomorphism. -/
theorem exists_opens_isIso_fstRestrict_iff (z : Z ⟶ B) (x : X ⟶ B) [Separated x]
    [FinitePresentation z] [Flat z] [Proper z]
    (σ : SchemesOver B) (p : FiberPoint z x σ) :
    ∃ V : (σ.left.left).Opens,
      ∀ {τ : SchemesOver B} (h : τ ⟶ σ),
        Nonempty (Over.mk h.left.left ⟶ Over.mk V.ι) ↔
          IsIso (fstRestrict (p.pullback h)) :=
  sorry

/-- A fibre point is the graph of a relative morphism if and only if
`pr₁|_Y : Y ⟶ Z_T` is an isomorphism. -/
theorem isIso_fstRestrict_iff_exists_graphPoint (z : Z ⟶ B) (x : X ⟶ B)
    [Separated x] [FinitePresentation z] [Flat z] [Proper z]
    (σ : SchemesOver B) (p : FiberPoint z x σ) :
    IsIso (fstRestrict p) ↔
      ∃ b : BaseChangeMorphism z x σ.hom, Rel p (graphPoint z x σ b) :=
  sorry

end AlgebraicGeometry.AlgebraicSpace.RelativeHom
