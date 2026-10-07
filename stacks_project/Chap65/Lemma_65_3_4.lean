module

public import Mathlib.AlgebraicGeometry.Scheme
public import Mathlib.CategoryTheory.Comma.Over.Basic
public import Mathlib.CategoryTheory.Limits.Shapes.BinaryProducts
public import Mathlib.CategoryTheory.MorphismProperty.Representable
public import ReasLib.CategoryTheory.MorphismProperty.Limits
import StacksCheckRecall

@[expose] public section

open CategoryTheory AlgebraicGeometry Limits MorphismProperty

universe u

variable {S : Scheme.{u}} {F₁ F₂ G₁ G₂ : (Over S)ᵒᵖ ⥤ Type u}
variable (a₁ : F₁ ⟶ G₁) (a₂ : F₂ ⟶ G₂)
variable (ha₁ : yoneda.relativelyRepresentable a₁) (ha₂ : yoneda.relativelyRepresentable a₂)

/- Lemma 65.3.4: let `S` be a scheme and let `Fᵢ`, `Gᵢ` be functors
`(Over S)ᵒᵖ ⥤ Type u` for `i = 1, 2`. If `aᵢ : Fᵢ ⟶ Gᵢ` are representable transformations
of functors, then the product morphism `a₁ × a₂ = prod.map a₁ a₂ : F₁ ⨯ F₂ ⟶ G₁ ⨯ G₂`
is a representable transformation of functors. -/
@[stacks 02WC]
#check (CategoryTheory.MorphismProperty.IsStableUnderBaseChange.prod_map a₁ a₂ ha₁ ha₂ :
  yoneda.relativelyRepresentable (prod.map a₁ a₂))
