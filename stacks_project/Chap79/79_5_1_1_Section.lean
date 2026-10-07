module

public import stacks_project.Chap78.Definition_78_11_1_Groupoid

/-!
# Source sections of a groupoid in algebraic spaces

A source section of a groupoid in algebraic spaces is a morphism `δ : U ⟶ R`
with `s ∘ δ = id_U`. These form the monoid `Γ` of the source, with identity `e`
and composition `δ₁ ∘ δ₂ = c(δ₁ ∘ t ∘ δ₂, δ₂)`.
-/

@[expose] public section

open CategoryTheory AlgebraicGeometry Limits

noncomputable section

universe u

namespace AlgebraicGeometry.GroupoidAlgebraicSpace

variable {S : Scheme.{u}} {B : AlgebraicSpace S} (G : GroupoidAlgebraicSpace B)

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

/-- The later arrow `δ₂ ≫ t ≫ δ₁` and the earlier arrow `δ₂` are composable. -/
theorem Section.comp_composable (δ₁ δ₂ : Section G) :
    (δ₂.arrow ≫ G.t ≫ δ₁.arrow) ≫ G.s = δ₂.arrow ≫ G.t := sorry

/-- The composite of two source sections is again a source section. -/
theorem Section.comp_source (δ₁ δ₂ : Section G) :
    G.compose (δ₂.arrow ≫ G.t ≫ δ₁.arrow) δ₂.arrow (Section.comp_composable G δ₁ δ₂) ≫
      G.s = 𝟙 G.U := sorry

/-- Composition of source sections: `δ₁ ∘ δ₂ = c(δ₁ ∘ t ∘ δ₂, δ₂)`. -/
def Section.comp (δ₁ δ₂ : Section G) : Section G :=
  Section.of G (G.compose (δ₂.arrow ≫ G.t ≫ δ₁.arrow) δ₂.arrow
      (Section.comp_composable G δ₁ δ₂))
    (Section.comp_source G δ₁ δ₂)

/-- The underlying arrow of a composite is the ambient groupoid composite. -/
theorem Section.comp_arrow (δ₁ δ₂ : Section G) :
    (Section.comp G δ₁ δ₂).arrow =
      G.compose (δ₂.arrow ≫ G.t ≫ δ₁.arrow) δ₂.arrow
        (Section.comp_composable G δ₁ δ₂) := rfl

end AlgebraicGeometry.GroupoidAlgebraicSpace
