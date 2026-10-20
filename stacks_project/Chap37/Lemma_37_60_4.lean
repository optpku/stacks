module

public import ReasLib.AlgebraicGeometry.Scheme.Morphism.PseudoCoherent.Composition
import StacksCheckRecall

open CategoryTheory

universe u

/- Lemma 37.60.4: A composition of pseudo-coherent morphisms of schemes is pseudo-coherent. -/
@[stacks 0681] #check (AlgebraicGeometry.PseudoCoherent.comp :
  ∀ {X Y Z : AlgebraicGeometry.Scheme.{u}} (f : X ⟶ Y) (g : Y ⟶ Z)
    [AlgebraicGeometry.PseudoCoherent f] [AlgebraicGeometry.PseudoCoherent g],
    AlgebraicGeometry.PseudoCoherent (f ≫ g))
