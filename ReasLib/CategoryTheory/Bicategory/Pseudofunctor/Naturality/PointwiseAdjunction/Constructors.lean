/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

import Mathlib.Tactic.CrossRefAttribute
public import ReasLib.CategoryTheory.Bicategory.Pseudofunctor.Naturality.Evaluation.At.Basic
public import ReasLib.CategoryTheory.Bicategory.Pseudofunctor.Naturality.PointwiseAdjunction.Components

/-!
# Constructors for pointwise adjunctions

This leaf constructs pointwise adjunction data by evaluation and under identity
and composition. The representation and component accessors remain in the
narrow `PointwiseAdjunction.Components` leaf.
-/

@[expose] public section

universe wB vB uB wD vD uD

namespace CategoryTheory

open scoped Bicategory Pseudofunctor.StrongTrans

namespace Pseudofunctor.StrongTrans.PointwiseAdjunction

variable {B : Type uB} [Bicategory.{wB, vB} B]
variable {D : Type uD} [Bicategory.{wD, vD} D]
variable {F G : Pseudofunctor B D}
variable {η : F ⟶ G}

/-- Pointwise adjunction data obtained by evaluating an adjunction in the pseudofunctor
bicategory. -/
@[stacks 0040 "pointwise adjunction obtained by evaluation"]
def ofAdjunction {θ : G ⟶ F} (adj : η ⊣ θ) :
    PointwiseAdjunction η := fun a ↦
  ⟨θ.app a, (evaluationAt D a).mapAdjunction adj⟩

/-- The right adjoint chosen by `ofAdjunction` is the corresponding component of the right
adjoint strong transformation. -/
@[simp]
theorem ofAdjunction.rightApp {θ : G ⟶ F} (adj : η ⊣ θ) (a : B) :
    (ofAdjunction adj).rightApp a = θ.app a := sorry

/-- The component adjunction of `ofAdjunction` is obtained by strict evaluation. -/
@[simp]
theorem ofAdjunction.adj {θ : G ⟶ F} (adj : η ⊣ θ) (a : B) :
    (ofAdjunction adj).adj a =
      (evaluationAt D a).mapAdjunction adj := sorry

/-- Identity strong transformations carry their canonical pointwise identity
adjunctions. -/
@[stacks 0040 "identity pointwise adjunction"]
def id (F : Pseudofunctor B D) :
    PointwiseAdjunction (StrongTrans.id F) := fun a ↦
  ⟨𝟙 (F.obj a), Bicategory.Adjunction.id (F.obj a)⟩

/-- The right adjoint in the canonical pointwise identity adjunction is the identity
`1`-morphism. -/
@[simp]
theorem id.rightApp (F : Pseudofunctor B D) (a : B) :
    (id F).rightApp a = 𝟙 (F.obj a) := sorry

/-- The adjunction in the canonical pointwise identity adjunction is the identity
adjunction. -/
@[simp]
theorem id.adj (F : Pseudofunctor B D) (a : B) :
    (id F).adj a =
      Bicategory.Adjunction.id (F.obj a) := sorry

/-- Pointwise adjunctions compose by composing left adjoints in the forward order and
right adjoints in the reverse order. -/
@[stacks 0040 "composition of pointwise adjunctions"]
def comp
    {H : Pseudofunctor B D} {η : F ⟶ G} {θ : G ⟶ H}
    (hη : PointwiseAdjunction η) (hθ : PointwiseAdjunction θ) :
    PointwiseAdjunction (η ≫ θ) := fun a ↦
  ⟨hθ.rightApp a ≫ hη.rightApp a, (hη.adj a).comp (hθ.adj a)⟩

/-- The chosen right adjoint of a composite pointwise adjunction is the reverse composite
of the chosen right adjoints. -/
@[simp]
theorem comp.rightApp
    {H : Pseudofunctor B D} {η : F ⟶ G} {θ : G ⟶ H}
    (hη : PointwiseAdjunction η) (hθ : PointwiseAdjunction θ)
    (a : B) :
    (comp hη hθ).rightApp a =
      hθ.rightApp a ≫ hη.rightApp a := sorry

/-- The component adjunction of a composite pointwise adjunction is the composite of the
component adjunctions. -/
@[simp]
theorem comp.adj
    {H : Pseudofunctor B D} {η : F ⟶ G} {θ : G ⟶ H}
    (hη : PointwiseAdjunction η) (hθ : PointwiseAdjunction θ)
    (a : B) :
    (comp hη hθ).adj a =
      (hη.adj a).comp (hθ.adj a) := sorry

/-- Strict evaluation of an identity adjunction recovers the canonical pointwise identity
adjunction. -/
@[simp]
theorem ofAdjunction.id (F : Pseudofunctor B D) :
    ofAdjunction (Bicategory.Adjunction.id F) =
      id F := sorry

/-- Strict evaluation sends composition of adjunctions to composition of their pointwise
adjunctions. -/
@[simp]
theorem ofAdjunction.comp
    {H : Pseudofunctor B D}
    {η : F ⟶ G} {ηr : G ⟶ F}
    {θ : G ⟶ H} {θr : H ⟶ G}
    (adjη : η ⊣ ηr) (adjθ : θ ⊣ θr) :
    ofAdjunction (adjη.comp adjθ) =
      comp (ofAdjunction adjη) (ofAdjunction adjθ) := sorry

/- Data audit (mathlib 4.32): `ofAdjunction`, `id`, and `comp` retain
their chosen right adjoints explicitly. Any `sorryAx` is confined to
evaluation coherence or readout equalities. -/

end Pseudofunctor.StrongTrans.PointwiseAdjunction

end CategoryTheory
