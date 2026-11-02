/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import Mathlib.CategoryTheory.MorphismProperty.Basic
public import Mathlib.CategoryTheory.Comma.Arrow

/-!
# Local presentation lifts

Existential source-cover conditions and universal comparison conditions are
kept separate. The three profile constructors below package the quantifiers
of Stacks 03MJ, 06FM and 0CIF. Their input chart types must contain the actual
commutative square (or invertible 2-cell) and the indicated target condition.
No locality theorem, algebraicity assumption, or choice of atlas is built in.
-/

@[expose] public section

namespace CategoryTheory.MorphismProperty

universe uC vC uD vD q

/-- Actual charts and their top arrows, with separate cover and comparison tests. -/
structure ChartFamily (C : Type uC) [Category.{vC} C]
    (D : Type uD) [CategoryStruct.{vD} D] where
  Chart : ∀ {X Y : D}, (X ⟶ Y) → Type q
  top : ∀ {X Y : D} {f : X ⟶ Y}, Chart f → Arrow C
  coversSource : ∀ {X Y : D} {f : X ⟶ Y}, Chart f → Prop
  goodComparison : ∀ {X Y : D} {f : X ⟶ Y}, Chart f → Prop

namespace ChartFamily

variable {C : Type uC} [Category.{vC} C] {D : Type uD} [CategoryStruct.{vD} D]

def «local» (A : ChartFamily.{uC, vC, uD, vD, q} C D)
    (P : MorphismProperty C) : MorphismProperty D :=
  fun _ _ f ↦ ∃ a : A.Chart f, A.coversSource a ∧ P (A.top a).hom

def forallLocal (A : ChartFamily.{uC, vC, uD, vD, q} C D)
    (P : MorphismProperty C) : MorphismProperty D :=
  fun _ _ f ↦ ∀ a : A.Chart f, A.goodComparison a → P (A.top a).hom

variable (Chart : ∀ {X Y : D}, (X ⟶ Y) → Type q)
    (top : ∀ {X Y : D} {f : X ⟶ Y}, Chart f → Arrow C)

/-- 03MJ profile. Input charts have scheme endpoints, étale vertical maps and
strict commutativity. Every chart is admissible for the universal test. -/
def etaleEtale
    (sourceSurjective : ∀ {X Y : D} {f : X ⟶ Y}, Chart f → Prop) :
    ChartFamily C D where
  Chart := Chart
  top := top
  coversSource := sourceSurjective
  goodComparison := fun _ ↦ True

/-- 06FM profile. Input charts have algebraic-space endpoints, a smooth target
map and an invertible commuting 2-cell. The existential test requires a smooth
surjective source map; only the universal test requires a smooth comparison
into the fibre product as well. -/
def smoothSmooth
    (sourceSmooth sourceSurjective comparisonSmooth :
      ∀ {X Y : D} {f : X ⟶ Y}, Chart f → Prop) : ChartFamily C D where
  Chart := Chart
  top := top
  coversSource := fun a ↦ sourceSmooth a ∧ sourceSurjective a
  goodComparison := fun a ↦ sourceSmooth a ∧ comparisonSmooth a

/-- 0CIF profile. Input charts have algebraic-space endpoints, a smooth target
map and an invertible commuting 2-cell. Both tests require an étale comparison
into the fibre product, not an étale source map. The existential test additionally
requires source surjectivity. A geometric equivalence of the two tests needs the
DM and locality hypotheses; no such equivalence is asserted by this constructor. -/
def etaleSmooth
    (sourceSurjective comparisonEtale :
      ∀ {X Y : D} {f : X ⟶ Y}, Chart f → Prop) : ChartFamily C D where
  Chart := Chart
  top := top
  coversSource := fun a ↦ comparisonEtale a ∧ sourceSurjective a
  goodComparison := comparisonEtale

variable {Chart top}

/-- Unfold the existential presentation test without selecting a chart. -/
theorem local_iff (A : ChartFamily.{uC, vC, uD, vD, q} C D)
    (P : MorphismProperty C) {X Y : D} (f : X ⟶ Y) :
    A.local P f ↔ ∃ a : A.Chart f, A.coversSource a ∧ P (A.top a).hom := Iff.rfl

/-- Unfold the universal comparison test. -/
theorem forallLocal_iff (A : ChartFamily.{uC, vC, uD, vD, q} C D)
    (P : MorphismProperty C) {X Y : D} (f : X ⟶ Y) :
    A.forallLocal P f ↔ ∀ a : A.Chart f,
      A.goodComparison a → P (A.top a).hom := Iff.rfl

end ChartFamily
end CategoryTheory.MorphismProperty
