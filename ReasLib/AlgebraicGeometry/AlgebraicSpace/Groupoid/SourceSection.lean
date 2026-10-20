/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.AlgebraicGeometry.AlgebraicSpace.Groupoid

/-!
# Composition of source sections in a groupoid in algebraic spaces
-/

@[expose] public section

open CategoryTheory AlgebraicGeometry Limits

noncomputable section

universe u

namespace AlgebraicGeometry.GroupoidAlgebraicSpace.SourceSection

variable {S : Scheme.{u}} [HasPullbacks (AlgebraicSpace S)]

/-- The later arrow `δ2 ≫ G.t ≫ δ1` and the earlier arrow `δ2` are composable
when `δ1` is a source section. -/
theorem composable {B : AlgebraicSpace S}
    (G : GroupoidAlgebraicSpace B) (δ1 δ2 : G.U ⟶ G.R)
    (hδ1 : δ1 ≫ G.s = 𝟙 G.U) :
    (δ2 ≫ G.t ≫ δ1) ≫ G.s = δ2 ≫ G.t := by
  simp [Category.assoc, hδ1]

/-- The composable pair `(δ2 ≫ G.t ≫ δ1, δ2)` as a morphism into `pullback G.s G.t`. -/
def pair {B : AlgebraicSpace S} (G : GroupoidAlgebraicSpace B)
    (δ1 δ2 : G.U ⟶ G.R) (hδ1 : δ1 ≫ G.s = 𝟙 G.U) (hδ2 : δ2 ≫ G.s = 𝟙 G.U) :
    G.U ⟶ pullback G.s G.t :=
  pullback.lift (δ2 ≫ G.t ≫ δ1) δ2 (composable G δ1 δ2 hδ1)

/-- The first projection of the source-section pair is the later arrow `δ2 ≫ G.t ≫ δ1`. -/
theorem pair_fst {B : AlgebraicSpace S}
    (G : GroupoidAlgebraicSpace B) (δ1 δ2 : G.U ⟶ G.R)
    (hδ1 : δ1 ≫ G.s = 𝟙 G.U) (hδ2 : δ2 ≫ G.s = 𝟙 G.U) :
    pair G δ1 δ2 hδ1 hδ2 ≫ pullback.fst G.s G.t = δ2 ≫ G.t ≫ δ1 := sorry

/-- The second projection of the source-section pair is the earlier arrow `δ2`. -/
theorem pair_snd {B : AlgebraicSpace S}
    (G : GroupoidAlgebraicSpace B) (δ1 δ2 : G.U ⟶ G.R)
    (hδ1 : δ1 ≫ G.s = 𝟙 G.U) (hδ2 : δ2 ≫ G.s = 𝟙 G.U) :
    pair G δ1 δ2 hδ1 hδ2 ≫ pullback.snd G.s G.t = δ2 := sorry

/-- Composition of two source sections as a morphism `G.U ⟶ G.R`. -/
def comp {B : AlgebraicSpace S} (G : GroupoidAlgebraicSpace B)
    (δ1 δ2 : G.U ⟶ G.R) (hδ1 : δ1 ≫ G.s = 𝟙 G.U) (hδ2 : δ2 ≫ G.s = 𝟙 G.U) :
    G.U ⟶ G.R :=
  G.compose (δ2 ≫ G.t ≫ δ1) δ2 (composable G δ1 δ2 hδ1)

/-- The composite of two source sections is again a source section. -/
theorem comp_source {B : AlgebraicSpace S}
    (G : GroupoidAlgebraicSpace B) (δ1 δ2 : G.U ⟶ G.R)
    (hδ1 : δ1 ≫ G.s = 𝟙 G.U) (hδ2 : δ2 ≫ G.s = 𝟙 G.U) :
    comp G δ1 δ2 hδ1 hδ2 ≫ G.s = 𝟙 G.U := sorry

/-- The composition of source sections is the ambient groupoid composition of the induced pair. -/
theorem comp_eq {B : AlgebraicSpace S}
    (G : GroupoidAlgebraicSpace B) (δ1 δ2 : G.U ⟶ G.R)
    (hδ1 : δ1 ≫ G.s = 𝟙 G.U) (hδ2 : δ2 ≫ G.s = 𝟙 G.U) :
    comp G δ1 δ2 hδ1 hδ2 =
      G.compose (δ2 ≫ G.t ≫ δ1) δ2 (composable G δ1 δ2 hδ1) := sorry

end AlgebraicGeometry.GroupoidAlgebraicSpace.SourceSection

namespace AlgebraicGeometry.GroupoidAlgebraicSpace

variable {S : Scheme.{u}} [HasPullbacks (AlgebraicSpace S)] {B : AlgebraicSpace S} (G : GroupoidAlgebraicSpace B)

/-- A source section of a groupoid in algebraic spaces: a morphism `δ : U ⟶ R`
satisfying `δ ≫ s = 𝟙 U`. -/
structure Section where
  /-- The underlying morphism `U ⟶ R`. -/
  arrow : G.U ⟶ G.R
  /-- The source of the section is the identity on objects. -/
  source : arrow ≫ G.s = 𝟙 G.U

/-- Build a source section from a morphism `U ⟶ R` with source the identity. -/
def Section.of (arrow : G.U ⟶ G.R) (source : arrow ≫ G.s = 𝟙 G.U) :
    Section G :=
  ⟨arrow, source⟩

/-- The underlying arrow of `Section.of` is the supplied morphism. -/
theorem Section.of_arrow (arrow : G.U ⟶ G.R) (source : arrow ≫ G.s = 𝟙 G.U) :
    (Section.of G arrow source).arrow = arrow := rfl

/-- Source sections with the same underlying arrow are equal. -/
theorem Section.ext {δ₁ δ₂ : Section G} (h : δ₁.arrow = δ₂.arrow) : δ₁ = δ₂ := sorry

/-- The identity section is the identity-arrow map `e`. -/
def Section.id : Section G :=
  Section.of G G.e G.identity_source

/-- The underlying arrow of the identity section is `e`. -/
theorem Section.id_arrow : (Section.id G).arrow = G.e := rfl

/-- Composition of source sections: `δ₁ ∘ δ₂ = c(δ₁ ∘ t ∘ δ₂, δ₂)`. -/
def Section.comp (δ₁ δ₂ : Section G) : Section G :=
  Section.of G (SourceSection.comp G δ₁.arrow δ₂.arrow δ₁.source δ₂.source)
    (SourceSection.comp_source G δ₁.arrow δ₂.arrow δ₁.source δ₂.source)

/-- The underlying arrow of a composite is the composition of the underlying source sections. -/
theorem Section.comp_arrow (δ₁ δ₂ : Section G) :
    (Section.comp G δ₁ δ₂).arrow =
      SourceSection.comp G δ₁.arrow δ₂.arrow δ₁.source δ₂.source := rfl

end AlgebraicGeometry.GroupoidAlgebraicSpace
