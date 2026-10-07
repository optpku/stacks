module

public import ReasLib.AlgebraicGeometry.Scheme.Morphism.Flat.Stalk
import StacksCheckRecall

@[expose] public section

open CategoryTheory

universe u

/- Lemma 38.10.10: if a locally finite-type scheme morphism `f : X ⟶ S` is flat at
`x : X`, then its canonical stalk map is essentially of finite presentation. -/
@[stacks 05I8]
#check
  (AlgebraicGeometry.Scheme.Hom.essFinitePresentation_stalkMap_of_flatAt :
    ∀ {X S : AlgebraicGeometry.Scheme.{u}} (f : X ⟶ S)
      [AlgebraicGeometry.LocallyOfFiniteType f]
      (x : X), f.flatAt x → (f.stalkMap x).hom.EssFinitePresentation)
