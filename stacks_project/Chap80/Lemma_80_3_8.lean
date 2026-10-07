module

public import Mathlib.CategoryTheory.MorphismProperty.Composition
public import stacks_project.Chap80.Definition_80_3_1_RelativelyRepresentable

/-!
# Composition of morphisms representable by algebraic spaces

The property of being representable by algebraic spaces is stable under
composition of maps of presheaves on schemes over `S`.
-/

@[expose] public section

open CategoryTheory AlgebraicGeometry MorphismProperty

universe u

namespace AlgebraicGeometry.AlgebraicSpace

/-- Lemma 80.3.8: let `S` be a scheme. For maps `a : F ⟶ G` and `b : G ⟶ H` of
presheaves on `(Sch/S)_fppf`, if `a` and `b` are representable by algebraic
spaces then so is `a ≫ b` (Stacks `b ∘ a`). -/
@[stacks 03Y1]
instance representableByAlgebraicSpaces.isStableUnderComposition {S : Scheme.{u}} :
    IsStableUnderComposition (@representableByAlgebraicSpaces S) := sorry

/-- If `a : F ⟶ G` and `b : G ⟶ H` are representable by algebraic spaces, then
so is the composite `a ≫ b`. -/
theorem representableByAlgebraicSpaces.comp {S : Scheme.{u}}
    {F G H : (Over S)ᵒᵖ ⥤ Type u} (a : F ⟶ G) (b : G ⟶ H)
    (ha : representableByAlgebraicSpaces a) (hb : representableByAlgebraicSpaces b) :
    representableByAlgebraicSpaces (a ≫ b) := sorry

end AlgebraicGeometry.AlgebraicSpace
