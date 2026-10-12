/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import ReasLib.AlgebraicGeometry.Scheme.Morphism.Fiber.SectionComponent

/-!
# Base change of fibre components selected by a section
-/

@[expose] public section

open CategoryTheory
open scoped AlgebraicGeometry

universe u

namespace AlgebraicGeometry.Scheme.Hom.Section

/-- In a pullback square compatible with sections, the component locus selected
by the pulled-back section is the inverse image of the original component locus. -/
theorem componentLocus_baseChange {X Y X' Y' : Scheme.{u}}
    (f : X ⟶ Y) (s : Y ⟶ X) (hs : s ≫ f = 𝟙 Y)
    (g : Y' ⟶ Y) (g' : X' ⟶ X) (f' : X' ⟶ Y')
    (hcart : IsPullback g' f' f g) (s' : Y' ⟶ X')
    (hs' : s' ≫ f' = 𝟙 Y') (hs_baseChange : s' ≫ g' = g ≫ s) :
    componentLocus f' s' hs' = g' ⁻¹' componentLocus f s hs := sorry

end AlgebraicGeometry.Scheme.Hom.Section
