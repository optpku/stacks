/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.AlgebraicGeometry.AlgebraicSpace.FinitePart.Pair

/-!
# Finite-part pairs containing a section graph

A variant of a finite-part pair `(a, Z)` for a morphism `f : X ⟶ Y` of algebraic
spaces over a scheme `S` together with a section `σ : Y ⟶ X` of `f`: the graph
`(1_T, σ ∘ a) : T ⟶ T ×_Y X` factors through the open subspace `Z`.
-/

@[expose] public section

open CategoryTheory AlgebraicGeometry Limits

noncomputable section

universe u

namespace AlgebraicGeometry.AlgebraicSpace

namespace FinitePart

/-- The two legs `1_T` and `σ ∘ a` agree over `Y` when `σ` is a section of `f`. -/
theorem sectionGraph_condition {S : Scheme.{u}} {X Y T : AlgebraicSpace S}
    (a : T ⟶ Y) (f : X ⟶ Y) (σ : Y ⟶ X) (hσ : σ ≫ f = 𝟙 Y) :
    𝟙 T ≫ a = (a ≫ σ) ≫ f := by
  simp only [Category.id_comp, Category.assoc, hσ, Category.comp_id]

/-- The graph morphism `(1_T, σ ∘ a) : T ⟶ T ×_Y X`. -/
def sectionGraph {S : Scheme.{u}} {X Y T : AlgebraicSpace S}
    (a : T ⟶ Y) (f : X ⟶ Y) (σ : Y ⟶ X) (hσ : σ ≫ f = 𝟙 Y) :
    T ⟶ pullback a f :=
  pullback.lift (𝟙 T) (a ≫ σ) (sectionGraph_condition a f σ hσ)

/-- The first component of the section graph is `1_T`. -/
theorem sectionGraph_fst {S : Scheme.{u}} {X Y T : AlgebraicSpace S}
    (a : T ⟶ Y) (f : X ⟶ Y) (σ : Y ⟶ X) (hσ : σ ≫ f = 𝟙 Y) :
    sectionGraph a f σ hσ ≫ pullback.fst a f = 𝟙 T :=
  sorry

/-- The second component of the section graph is `σ ∘ a`. -/
theorem sectionGraph_snd {S : Scheme.{u}} {X Y T : AlgebraicSpace S}
    (a : T ⟶ Y) (f : X ⟶ Y) (σ : Y ⟶ X) (hσ : σ ≫ f = 𝟙 Y) :
    sectionGraph a f σ hσ ≫ pullback.snd a f = a ≫ σ :=
  sorry

/-- A finite-part pair `(a, Z)` through which the section graph `(1_T, σ ∘ a)`
factors. -/
structure WithSection {S : Scheme.{u}} {X Y : AlgebraicSpace S} (f : X ⟶ Y)
    (σ : Y ⟶ X) (hσ : σ ≫ f = 𝟙 Y) (T : AlgebraicSpace S)
    extends FinitePart f T where
  /-- The graph `(1_T, σ ∘ a)` factors through the open subspace `Z`. -/
  factors : ∃ ℓ : T ⟶ Z.X, ℓ ≫ Z.ι = sectionGraph a f σ hσ

namespace WithSection

/-- Build a variant pair from a finite-part pair whose section graph factors
through `Z`. -/
def of {S : Scheme.{u}} {X Y T : AlgebraicSpace S} {f : X ⟶ Y} {σ : Y ⟶ X}
    (hσ : σ ≫ f = 𝟙 Y) (p : FinitePart f T)
    (h : ∃ ℓ : T ⟶ p.Z.X, ℓ ≫ p.Z.ι = sectionGraph p.a f σ hσ) :
    WithSection f σ hσ T where
  toFinitePart := p
  factors := h

/-- A variant pair consists of an open immersion into `T ×_Y X` whose restricted
first projection is finite and through which the section graph factors. -/
theorem spec {S : Scheme.{u}} {X Y T : AlgebraicSpace S} {f : X ⟶ Y}
    {σ : Y ⟶ X} {hσ : σ ≫ f = 𝟙 Y} (p : WithSection f σ hσ T) :
    IsOpenImmersion p.Z.ι ∧ IsFinite p.pr ∧
      ∃ ℓ : T ⟶ p.Z.X, ℓ ≫ p.Z.ι = sectionGraph p.a f σ hσ :=
  sorry

/-- The chosen factorization of the section graph through `Z`. -/
def lift {S : Scheme.{u}} {X Y T : AlgebraicSpace S} {f : X ⟶ Y} {σ : Y ⟶ X}
    {hσ : σ ≫ f = 𝟙 Y} (p : WithSection f σ hσ T) : T ⟶ p.Z.X :=
  Classical.choose p.factors

/-- The chosen lift composites with the open inclusion to the section graph. -/
theorem lift_comp {S : Scheme.{u}} {X Y T : AlgebraicSpace S} {f : X ⟶ Y}
    {σ : Y ⟶ X} {hσ : σ ≫ f = 𝟙 Y} (p : WithSection f σ hσ T) :
    p.lift ≫ p.Z.ι = sectionGraph p.a f σ hσ :=
  sorry

/-- The type of variant pairs for a scheme `T` over `S`, recovered as an
algebraic space via `ofOver`. -/
abbrev over {S : Scheme.{u}} {X Y : AlgebraicSpace S} (f : X ⟶ Y) (σ : Y ⟶ X)
    (hσ : σ ≫ f = 𝟙 Y) (T : Over S) :=
  WithSection f σ hσ (ofOver T)

end WithSection

end FinitePart

end AlgebraicGeometry.AlgebraicSpace
