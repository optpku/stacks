module

public import ReasLib.AlgebraicGeometry.AlgebraicSpace.Representable.Composition
import StacksCheckRecall

/-!
# Composition of morphisms representable by algebraic spaces

The property of being representable by algebraic spaces is stable under
composition of maps of presheaves on schemes over `S`.
-/

@[expose] public section

open CategoryTheory AlgebraicGeometry MorphismProperty

universe u

/- Lemma 80.3.8: let `S` be a scheme. For maps `a : F ⟶ G` and `b : G ⟶ H` of
presheaves on `(Sch/S)_fppf`, if `a` and `b` are representable by algebraic
spaces then so is `a ≫ b` (Stacks `b ∘ a`). -/
@[stacks 03Y1] #check
  (AlgebraicGeometry.AlgebraicSpace.representableByAlgebraicSpaces.isStableUnderComposition :
    ∀ {S : Scheme.{u}}, MorphismProperty.IsStableUnderComposition
      (@AlgebraicGeometry.AlgebraicSpace.representableByAlgebraicSpaces S))

#check (AlgebraicGeometry.AlgebraicSpace.representableByAlgebraicSpaces.comp :
  ∀ {S : Scheme.{u}} {F G H : (Over S)ᵒᵖ ⥤ Type u} (a : F ⟶ G) (b : G ⟶ H)
    (ha : AlgebraicGeometry.AlgebraicSpace.representableByAlgebraicSpaces a)
    (hb : AlgebraicGeometry.AlgebraicSpace.representableByAlgebraicSpaces b),
    AlgebraicGeometry.AlgebraicSpace.representableByAlgebraicSpaces (a ≫ b))
