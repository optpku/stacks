module

public import ReasLib.AlgebraicGeometry.AlgebraicSpace.Module.IdealProduct.Pushforward
import StacksCheckRecall

@[expose] public section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
open AlgebraicGeometry.AlgebraicSpace AlgebraicGeometry.AlgebraicSpace.Modules

universe u

/- Lemma 69.17.2: for an affine morphism of algebraic spaces, multiplication of a
quasi-coherent direct image by a quasi-coherent ideal agrees with direct image of
the product with the inverse-image ideal. -/
@[stacks 0GF8] #check
  (AlgebraicGeometry.AlgebraicSpace.Modules.idealProductSubobject_pushforward_eq_map_of_affine :
    ∀ {S : Scheme.{u}} {X Y : AlgebraicSpace S} (f : Y ⟶ X) [Affine f]
      (F : Y.Modules) [F.IsQuasicoherent] (I : IdealSubobject X) [IsQuasiCoherent I],
      idealProductSubobject I ((pushforward f).obj F) =
        (Subobject.map
            ((pushforward f).map
              (idealProductSubobject (I.pullback f) F).arrow)).obj ⊤)
