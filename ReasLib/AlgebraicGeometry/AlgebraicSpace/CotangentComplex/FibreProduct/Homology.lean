module

public import Mathlib.Algebra.Category.ModuleCat.Ulift
public import Mathlib.Algebra.Homology.DerivedCategory.HomologySequence
public import Mathlib.CategoryTheory.IsomorphismClasses
public import ReasLib.AlgebraicGeometry.AlgebraicSpace.CotangentComplex.FibreProduct
public import ReasLib.AlgebraicGeometry.AlgebraicSpace.CotangentComplex.Stalk
public import ReasLib.AlgebraicGeometry.AlgebraicSpace.EtaleLocalRing.FibreProduct
import Mathlib.Tactic.CrossRefAttribute

/-!
# Homology of the fibre-product cotangent cone
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits
open AlgebraicGeometry AlgebraicGeometry.AlgebraicSpace
open AlgebraicGeometry.AlgebraicSpace.GeometricPoint
open AlgebraicGeometry.AlgebraicSpace.Cotangent

noncomputable section

universe u

namespace AlgebraicGeometry.AlgebraicSpace.Cotangent.FibreProduct

variable {S : Scheme.{u}} {B X Y : AlgebraicSpace S}

/-- The fibre-product cotangent cone has zero homology in degrees zero and minus one. -/
@[stacks 09DM]
theorem cone_homology_isZero_of_eq_zero_or_negOne (f : X ⟶ B) (g : Y ⟶ B) {i : ℤ}
    (hi : i = 0 ∨ i = -1) :
    IsZero
      ((DerivedCategory.homologyFunctor (CommModules (pullback f g)) i).obj (cone f g)) :=
  sorry

/-- At a geometric point `(x̄, ȳ)` of `X ×_B Y`, the degree minus two homology stalk
of the fibre-product cotangent cone is isomorphic to
`Tor_1^R(A, 𝒪_{Y, ȳ}) ⊗_{A ⊗[R] 𝒪_{Y, ȳ}} C` as
modules over `C`, where `R = 𝒪_{B, b̄}`, `A = 𝒪_{X, x̄}`, and
`C = 𝒪_{X ×_B Y, (x̄, ȳ)}`. -/
@[stacks 09DM]
theorem cone_homology_negTwo_stalk_isIsomorphic_tor (f : X ⟶ B) (g : Y ⟶ B)
    (xybar : GeometricPoint (pullback f g)) :
    IsIsomorphic
      (commModulesStalk xybar
        ((DerivedCategory.homologyFunctor (CommModules (pullback f g)) (-2)).obj (cone f g)))
      ((ModuleCat.uliftFunctor.{u + 1, u}
          (AlgebraicGeometry.AlgebraicSpace.FibreProduct.stalkW f g xybar)).obj
        (AlgebraicGeometry.AlgebraicSpace.FibreProduct.torOneTensorStalk f g xybar)) :=
  sorry

end AlgebraicGeometry.AlgebraicSpace.Cotangent.FibreProduct
