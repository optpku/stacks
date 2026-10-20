module

public import ReasLib.AlgebraicGeometry.AlgebraicSpace.CotangentComplex.FibreProduct.Homology
import StacksCheckRecall

open CategoryTheory CategoryTheory.Limits
open AlgebraicGeometry AlgebraicGeometry.AlgebraicSpace
open AlgebraicGeometry.AlgebraicSpace.Cotangent
open AlgebraicGeometry.AlgebraicSpace.Cotangent.FibreProduct

universe u

/- Lemma 92.28.2 (1): The fibre-product cotangent cone has zero homology in degrees
zero and minus one. -/
@[stacks 09DM] #check
  (AlgebraicGeometry.AlgebraicSpace.Cotangent.FibreProduct.cone_homology_isZero_of_eq_zero_or_negOne :
    ∀ {S : Scheme.{u}} {B X Y : AlgebraicSpace S} (f : X ⟶ B) (g : Y ⟶ B) {i : ℤ},
      i = 0 ∨ i = -1 →
        IsZero ((DerivedCategory.homologyFunctor (CommModules (pullback f g)) i).obj
          (cone f g)))

/- Lemma 92.28.2 (2): At each geometric point of the fibre product, the degree minus
two homology stalk is Tor_1 of the factor local rings over the base local ring,
extended to the fibre-product local ring. -/
@[stacks 09DM] #check
  (AlgebraicGeometry.AlgebraicSpace.Cotangent.FibreProduct.cone_homology_negTwo_stalk_isIsomorphic_tor :
    ∀ {S : Scheme.{u}} {B X Y : AlgebraicSpace S} (f : X ⟶ B) (g : Y ⟶ B)
      (xybar : GeometricPoint (pullback f g)),
      IsIsomorphic
        (commModulesStalk xybar
          ((DerivedCategory.homologyFunctor (CommModules (pullback f g)) (-2)).obj (cone f g)))
        ((ModuleCat.uliftFunctor.{u + 1, u}
          (AlgebraicGeometry.AlgebraicSpace.FibreProduct.stalkW f g xybar)).obj
            (AlgebraicGeometry.AlgebraicSpace.FibreProduct.torOneTensorStalk f g xybar)))
