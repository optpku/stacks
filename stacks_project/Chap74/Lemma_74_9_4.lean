module

public import ReasLib.AlgebraicGeometry.AlgebraicSpace.Regular.Descent
import StacksCheckRecall

@[expose] public section

open CategoryTheory AlgebraicGeometry CategoryTheory.ObjectProperty

universe u

namespace AlgebraicGeometry.AlgebraicSpace

/- Lemma 74.9.4: If `f : X ⟶ Y` is a morphism of algebraic spaces that is locally
of finite presentation, flat, and surjective, and `X` is regular, then
`Y` is regular. -/
@[stacks 06MK] #check
  (AlgebraicGeometry.AlgebraicSpace.IsRegular.of_locallyOfFinitePresentation_flat_surjective :
    ∀ {S : Scheme.{u}} {X Y : AlgebraicSpace S} (f : X ⟶ Y)
      [LocallyOfFinitePresentation f] [Flat f] [Surjective f] [IsRegular X], IsRegular Y)

#check (AlgebraicGeometry.AlgebraicSpace.isRegular_inheritedFromSource :
  ∀ {S : Scheme.{u}},
    InheritedFromSource (@IsRegular S : ObjectProperty (AlgebraicSpace S))
      ((@LocallyOfFinitePresentation S : MorphismProperty (AlgebraicSpace S)) ⊓
        (@Flat S : MorphismProperty (AlgebraicSpace S)) ⊓
        (@Surjective S : MorphismProperty (AlgebraicSpace S))))

end AlgebraicGeometry.AlgebraicSpace
