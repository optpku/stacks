module

public import stacks_project.Chap65.Lemma_65_12_4_Immersion
public import ReasLib.AlgebraicGeometry.AlgebraicSpace.Immersion.Composition
import StacksCheckRecall

/-!
# Composition of immersions of algebraic spaces

A composition of immersions, closed immersions, or open immersions of algebraic
spaces over a scheme `S` is again an immersion, closed immersion, or open
immersion respectively.
-/

@[expose] public section

open CategoryTheory AlgebraicGeometry CategoryTheory.MorphismProperty

universe u

namespace AlgebraicGeometry.AlgebraicSpace

/- Lemma 65.12.2 (1): a composition of immersions of algebraic spaces over a scheme `S` is an
immersion of algebraic spaces over `S`. -/
@[stacks 02YV] #check (AlgebraicGeometry.AlgebraicSpace.IsImmersion.comp :
  ∀ {S : Scheme.{u}} {F G H : AlgebraicSpace S}
    (f : F ⟶ G) (g : G ⟶ H) [IsImmersion f] [IsImmersion g], IsImmersion (f ≫ g))

/- Lemma 65.12.2 (2): a composition of closed immersions of algebraic spaces over a scheme `S`
is a closed immersion of algebraic spaces over `S`. -/
@[stacks 02YV] #check (AlgebraicGeometry.AlgebraicSpace.IsClosedImmersion.comp :
  ∀ {S : Scheme.{u}} {F G H : AlgebraicSpace S}
    (f : F ⟶ G) (g : G ⟶ H) [IsClosedImmersion f] [IsClosedImmersion g],
    IsClosedImmersion (f ≫ g))

/- Lemma 65.12.2 (3): a composition of open immersions of algebraic spaces over a scheme `S` is
an open immersion of algebraic spaces over `S`. -/
@[stacks 02YV] #check (AlgebraicGeometry.AlgebraicSpace.IsOpenImmersion.comp :
  ∀ {S : Scheme.{u}} {F G H : AlgebraicSpace S}
    (f : F ⟶ G) (g : G ⟶ H) [IsOpenImmersion f] [IsOpenImmersion g],
    IsOpenImmersion (f ≫ g))

#check (AlgebraicGeometry.AlgebraicSpace.isImmersion_isStableUnderComposition :
  ∀ {S : Scheme.{u}},
    MorphismProperty.IsStableUnderComposition
      (@IsImmersion S : MorphismProperty (AlgebraicSpace S)))

#check (AlgebraicGeometry.AlgebraicSpace.isClosedImmersion_isStableUnderComposition :
  ∀ {S : Scheme.{u}},
    MorphismProperty.IsStableUnderComposition
      (@IsClosedImmersion S : MorphismProperty (AlgebraicSpace S)))

#check (AlgebraicGeometry.AlgebraicSpace.isOpenImmersion_isStableUnderComposition :
  ∀ {S : Scheme.{u}},
    MorphismProperty.IsStableUnderComposition
      (@IsOpenImmersion S : MorphismProperty (AlgebraicSpace S)))

end AlgebraicGeometry.AlgebraicSpace
