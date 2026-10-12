/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import Mathlib.CategoryTheory.Widesubcategory
import Mathlib.Tactic.CrossRefAttribute

/-!
# Restricting functors to wide subcategories

A functor carrying one multiplicative morphism property into another restricts canonically to
the corresponding wide subcategories. This is the morphism-property analogue of
`ObjectProperty.FullSubcategory.restrict`.
-/

@[expose] public section

universe uC vC uD vD

namespace CategoryTheory.MorphismProperty.WideSubcategory

variable {C : Type uC} [Category.{vC} C]
variable {D : Type uD} [Category.{vD} D]
variable {P : MorphismProperty C} {Q : MorphismProperty D}
variable [P.IsMultiplicative] [Q.IsMultiplicative]

/-- The image object in the target wide subcategory. Wide subcategories retain every ambient
object, so no property witness is needed here. -/
def mapObj (F : C ⥤ D) (X : CategoryTheory.WideSubcategory P) :
    CategoryTheory.WideSubcategory Q :=
  ⟨F.obj X.obj⟩

/-- Apply a property-preserving functor to a morphism of a wide subcategory. The underlying
morphism is exactly the ambient functor's image. -/
def mapHom
    (F : C ⥤ D) (hF : P ≤ Q.inverseImage F)
    {X Y : CategoryTheory.WideSubcategory P} (f : X ⟶ Y) :
    mapObj (Q := Q) F X ⟶ mapObj (Q := Q) F Y :=
  ⟨F.map f.hom, hF _ f.property⟩

/-- Mapping the identity morphism of a wide subcategory gives the target identity. -/
theorem mapHom_id
    (F : C ⥤ D) (hF : P ≤ Q.inverseImage F)
    (X : CategoryTheory.WideSubcategory P) :
    mapHom F hF (𝟙 X) = 𝟙 (mapObj (Q := Q) F X) := sorry

/-- Mapping a composite in a wide subcategory gives the composite of the mapped morphisms. -/
theorem mapHom_comp
    (F : C ⥤ D) (hF : P ≤ Q.inverseImage F)
    {X Y Z : CategoryTheory.WideSubcategory P} (f : X ⟶ Y) (g : Y ⟶ Z) :
    mapHom F hF (f ≫ g) = mapHom F hF f ≫ mapHom F hF g := sorry

/-- Restrict a functor to wide subcategories selected by multiplicative morphism properties. -/
@[stacks 03WQ "restriction of a functor to wide subcategories"]
def restrict (F : C ⥤ D) (hF : P ≤ Q.inverseImage F) :
    CategoryTheory.WideSubcategory P ⥤ CategoryTheory.WideSubcategory Q where
  obj := mapObj (Q := Q) F
  map := mapHom F hF
  map_id := mapHom_id F hF
  map_comp := mapHom_comp F hF

namespace restrict

/-- The underlying object of a restricted wide-subcategory functor is the image under the
ambient functor. -/
@[simp]
theorem obj_obj
    (F : C ⥤ D) (hF : P ≤ Q.inverseImage F)
    (X : CategoryTheory.WideSubcategory P) :
    ((restrict F hF).obj X).obj = F.obj X.obj := sorry

/-- The underlying morphism of a restricted wide-subcategory functor is the image under the
ambient functor. -/
@[simp]
theorem map_hom
    (F : C ⥤ D) (hF : P ≤ Q.inverseImage F)
    {X Y : CategoryTheory.WideSubcategory P} (f : X ⟶ Y) :
    ((restrict F hF).map f).hom = F.map f.hom := sorry

/-- Forgetting the target wide-subcategory condition recovers the ambient functor after the
source inclusion. -/
theorem comp_inclusion
    (F : C ⥤ D) (hF : P ≤ Q.inverseImage F) :
    restrict F hF ⋙ wideSubcategoryInclusion Q =
      wideSubcategoryInclusion P ⋙ F := sorry

end restrict

/- Axiom audit: object and morphism data are the explicit ambient images. Deferred axioms occur
only in the functor-law and equality proofs. -/

end CategoryTheory.MorphismProperty.WideSubcategory
