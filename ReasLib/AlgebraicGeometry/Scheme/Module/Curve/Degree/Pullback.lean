module

public import ReasLib.AlgebraicGeometry.Scheme.Module.Curve.Degree.FiniteLocallyFree
public import ReasLib.AlgebraicGeometry.Scheme.Module.Curve.Degree.Tensor
public import ReasLib.AlgebraicGeometry.Scheme.Morphism.Curve.Finite

/-!
# Degrees under pullback along morphisms of proper curves

Pullback along a dominant morphism of proper curves multiplies the degree of a finite locally
free module by the induced function-field degree.
-/

@[expose] public section

open AlgebraicGeometry
open CategoryTheory
open scoped AlgebraicGeometry

noncomputable section

universe u

namespace AlgebraicGeometry.Scheme.Modules

variable {k : Type u} [Field k]
variable {X Y : Over (Spec (CommRingCat.of k))}

/-- Dominant pullback preserves the dimension of the fiber at the generic point. -/
theorem fiberFinrank_pullback_genericPoint
    [Curve X] [Curve Y] (f : X ⟶ Y) [IsDominant f.left] (ℰ : Y.left.Modules) :
    fiberFinrank ((pullback f.left).obj ℰ) (genericPoint X.left) =
      fiberFinrank ℰ (genericPoint Y.left) := sorry

/-- Pullback along a dominant morphism of proper curves multiplies the fixed-rank curve degree
by the induced function-field degree. -/
theorem curveDegree_pullback_eq_inducedFunctionFieldDegree_mul_of_rank
    [Curve X] [Curve Y] [IsProper X.hom] [IsProper Y.hom]
    (f : X ⟶ Y) [IsDominant f.left] (ℰ : Y.left.Modules) (n : ℕ)
    [IsFiniteLocallyFreeOfRank n ℰ] :
    curveDegree X.hom (topologicalKrullDim_eq_one X).le
        ((pullback f.left).obj ℰ) n =
      (f.left.inducedFunctionFieldDegree : ℤ) *
        curveDegree Y.hom (topologicalKrullDim_eq_one Y).le ℰ n := sorry

/-- Pullback along a dominant morphism of proper curves multiplies the degree of a finite locally
free module by the induced function-field degree. -/
@[stacks 0AYZ]
theorem curveDegree_pullback_eq_inducedFunctionFieldDegree_mul
    [Curve X] [Curve Y] [IsProper X.hom] [IsProper Y.hom]
    (f : X ⟶ Y) [IsDominant f.left] (ℰ : Y.left.Modules) [IsFiniteLocallyFree ℰ] :
    curveDegreeOfFiniteLocallyFree ((pullback f.left).obj ℰ) =
      (f.left.inducedFunctionFieldDegree : ℤ) * curveDegreeOfFiniteLocallyFree ℰ := sorry

end AlgebraicGeometry.Scheme.Modules
