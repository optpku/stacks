module

public import ReasLib.AlgebraicGeometry.AlgebraicSpace.Module.Ample.Finite
import StacksCheckRecall

open AlgebraicGeometry AlgebraicGeometry.AlgebraicSpace
open CategoryTheory CategoryTheory.MonoidalCategory

universe u

namespace AlgebraicGeometry.AlgebraicSpace.Modules

/- Lemma 69.21.2: let `R` be a Noetherian ring, let `f : Y ⟶ X` be a finite
surjective morphism of algebraic spaces proper over `R`, and let `L` be an
invertible `𝒪_X`-module. Then `X` is a scheme and `L` is ample if and only if
`Y` is a scheme and `f^* L` is ample. -/
@[stacks 0GFB] #check
  (AlgebraicGeometry.AlgebraicSpace.Modules.isSchemeAndAmple_iff_pullback_of_isFinite_surjective :
    ∀ {R : Type u} [CommRing R] [IsNoetherianRing R]
      {X Y : AlgebraicSpace (Spec (CommRingCat.of R))}
      (πX : X ⟶ ofOver (Over.mk (𝟙 (Spec (CommRingCat.of R))))) [Proper πX]
      (πY : Y ⟶ ofOver (Over.mk (𝟙 (Spec (CommRingCat.of R))))) [Proper πY]
      (f : Y ⟶ X) [IsFinite f] [Surjective f]
      (L : X.Modules) [isInvertibleObject L],
      isSchemeAndAmple L ↔ isSchemeAndAmple ((pullback f).obj L))

end AlgebraicGeometry.AlgebraicSpace.Modules
