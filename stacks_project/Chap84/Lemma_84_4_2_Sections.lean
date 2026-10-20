module

public import Mathlib.AlgebraicGeometry.AffineScheme
public import ReasLib.CategoryTheory.Sites.Topos.Sections
public import ReasLib.AlgebraicGeometry.AlgebraicSpace.SpecialFiber
public import ReasLib.AlgebraicGeometry.AlgebraicSpace.EtaleSite.Sections
public import stacks_project.Chap65.Lemma_65_7_3_Pullback
public import stacks_project.Chap66.Definition_66_4_1_Points
public import stacks_project.Chap66.Lemma_66_18_8_Topos
public import stacks_project.Chap67.Lemma_67_24_2_FieldPoints

/-!
# Special-fibre inclusion and small étale global-section restriction

The canonical special-fibre inclusion and restriction of compatible sections
are imported from their mathematical owners. The legacy inclusion name remains
available for existing consumers.
-/

@[expose] public section

open CategoryTheory AlgebraicGeometry CategoryTheory.Limits
open scoped MorphismOfTopoiIn

noncomputable section

universe u

namespace AlgebraicGeometry.AlgebraicSpace

/-- The morphism `Spec(A / I) ⟶ Spec A` in `AlgebraicSpace (Spec A)`. -/
abbrev ofOverSpecQuotientι {A : Type u} [CommRing A] (I : Ideal A) :
    ofOver (Over.mk (Spec.map (CommRingCat.ofHom (Ideal.Quotient.mk I)))) ⟶
      ofOver (Over.mk (𝟙 (Spec (CommRingCat.of A)))) :=
  specQuotientι I

end AlgebraicGeometry.AlgebraicSpace
