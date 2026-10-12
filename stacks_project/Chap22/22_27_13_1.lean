/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import ReasLib.CategoryTheory.Pretriangulated.Triangle.Completion
public import ReasLib.Algebra.Homology.HomotopyCategory.MappingConeIso
import StacksCheckRecall

@[expose] public section

open CategoryTheory CategoryTheory.Pretriangulated

universe v u

variable {C : Type u} [Category.{v} C] [Limits.HasZeroObject C]
variable [HasShift C ℤ] [Preadditive C]
variable [∀ n : ℤ, (shiftFunctor C n).Additive] [Pretriangulated C]
variable {X Y Z Z' : C} {f : X ⟶ Y}
variable {g : Y ⟶ Z} {h : Z ⟶ X⟦(1 : ℤ)⟧}
variable {g' : Y ⟶ Z'} {h' : Z' ⟶ X⟦(1 : ℤ)⟧}
variable (hT : Triangle.mk f g h ∈ distTriang C)
variable (hT' : Triangle.mk f g' h' ∈ distTriang C)

/- Equation 22.27.13.1 [09QV]: two distinguished triangles with the same first morphism are
isomorphic through the identities on their first two vertices. Applied to the standard
mapping-cone triangle, the third component is the dotted comparison isomorphism in the source. -/
@[stacks 09QV] #check
  (Triangle.existsIsoOfSameMor₁ hT hT' :
    ∃ e : Triangle.mk f g h ≅ Triangle.mk f g' h',
      e.hom.hom₁ = 𝟙 X ∧ e.hom.hom₂ = 𝟙 Y)

/- Standard mapping-cone triangles in a homotopy category are distinguished. -/
#check @HomotopyCategory.mappingCone_triangleh_distinguished
