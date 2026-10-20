/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

import Mathlib.Tactic.CrossRefAttribute
public import ReasLib.CategoryTheory.Bicategory.Pseudofunctor.Naturality.StrongTrans.Category

public import Mathlib.CategoryTheory.Bicategory.Adjunction.Adj

/-!
# Pointwise adjunction data for strong transformations

This leaf owns the canonical pointwise family of mathlib
`Bicategory.RightAdjoint` objects and its component accessors. Evaluation,
identity, and composition constructors live in `PointwiseAdjunction.Constructors`.
-/

@[expose] public section

universe wB vB uB wD vD uD

namespace CategoryTheory

open scoped Bicategory Pseudofunctor.StrongTrans

namespace Pseudofunctor.StrongTrans

variable {B : Type uB} [Bicategory.{wB, vB} B]
variable {D : Type uD} [Bicategory.{wD, vD} D]
variable {F G : Pseudofunctor B D}

/-- Chosen pointwise right adjoints of the components of a strong transformation.

The family uses mathlib's canonical `Bicategory.RightAdjoint` owner at each source object.
This is the weakest componentwise hypothesis under which `η` can act between the
pseudofunctors `F.mapAdj` and `G.mapAdj`. -/
@[stacks 0040 "pointwise right adjoints of a strong transformation"]
abbrev PointwiseAdjunction (η : F ⟶ G) :=
  ∀ a : B, Bicategory.RightAdjoint (η.app a)

namespace PointwiseAdjunction

variable {η : F ⟶ G}

/-- The chosen bundled right adjoint of the component at `a`. -/
@[stacks 0040 "chosen component right adjoint"]
def rightAdjoint (h : PointwiseAdjunction η) (a : B) :
    Bicategory.RightAdjoint (η.app a) :=
  h a

/-- The underlying right-adjoint `1`-morphism at `a`. -/
def rightApp (h : PointwiseAdjunction η) (a : B) : G.obj a ⟶ F.obj a :=
  (h.rightAdjoint a).right

/-- The chosen component adjunction at `a`. -/
def adj (h : PointwiseAdjunction η) (a : B) : η.app a ⊣ h.rightApp a :=
  (h.rightAdjoint a).adj

/-- A pointwise adjunction regarded as a `1`-morphism in the bicategory of adjunctions. -/
def app (h : PointwiseAdjunction η) (a : B) :
    Bicategory.Adj.mk (F.obj a) ⟶ Bicategory.Adj.mk (G.obj a) :=
  ⟨h.adj a⟩

/-- The left adjoint of the component adjunction is the original strong-transformation
component. -/
@[simp]
theorem app.l (h : PointwiseAdjunction η) (a : B) :
    (h.app a).l = η.app a := sorry

/-- The right adjoint of the component adjunction is the chosen pointwise right adjoint. -/
@[simp]
theorem app.r (h : PointwiseAdjunction η) (a : B) :
    (h.app a).r = h.rightApp a := sorry

/-- The adjunction stored by a component is the supplied pointwise adjunction. -/
@[simp]
theorem app.adj (h : PointwiseAdjunction η) (a : B) :
    (h.app a).adj = h.adj a := sorry

/- Data audit (mathlib 4.32): `PointwiseAdjunction` is definitionally a family
of `Bicategory.RightAdjoint` objects, and `app` retains each chosen right
adjoint literally. Any `sorryAx` is confined to projection equalities. -/

end PointwiseAdjunction

end Pseudofunctor.StrongTrans

end CategoryTheory
