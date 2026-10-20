module

public import Mathlib.AlgebraicGeometry.Morphisms.UniversallyClosed
public import ReasLib.AlgebraicGeometry.AffineSpace.MorphismProperties

@[expose] public section

open CategoryTheory
open scoped AlgebraicGeometry

noncomputable section

universe u

namespace AlgebraicGeometry.AffineSpace

/-- The endomorphism of the affine line over `Spec (.of k)` that squares its coordinate. -/
def squareMap (k : Type u) [Field k] :
    𝔸(ULift.{u} (Fin 1); Spec (.of k)) ⟶ 𝔸(ULift.{u} (Fin 1); Spec (.of k)) :=
  homOfVector (𝔸(ULift.{u} (Fin 1); Spec (.of k)) ↘ Spec (.of k)) fun i ↦
    coord (Spec (.of k)) i ^ 2

/-- Pullback by the squaring endomorphism sends the affine-line coordinate to its square. -/
theorem squareMap_appTop_coord (k : Type u) [Field k] :
    (squareMap k).appTop (coord (Spec (.of k)) (ULift.up (0 : Fin 1))) =
      coord (Spec (.of k)) (ULift.up (0 : Fin 1)) ^ 2 := sorry

/-- The squaring endomorphism commutes with the affine-line projection to its base. -/
theorem squareMap_over (k : Type u) [Field k] :
    squareMap k ≫ (𝔸(ULift.{u} (Fin 1); Spec (.of k)) ↘ Spec (.of k)) =
      𝔸(ULift.{u} (Fin 1); Spec (.of k)) ↘ Spec (.of k) := sorry

/-- The squaring endomorphism of the affine line over a field is surjective. -/
instance squareMap_surjective (k : Type u) [Field k] : Surjective (squareMap k) := sorry

/-- The squaring endomorphism of the affine line over a field is flat. -/
instance squareMap_flat (k : Type u) [Field k] : Flat (squareMap k) := sorry

/-- The squaring endomorphism of the affine line over a field is locally of finite presentation. -/
instance squareMap_locallyOfFinitePresentation (k : Type u) [Field k] :
    LocallyOfFinitePresentation (squareMap k) := sorry

/-- The squaring endomorphism of the affine line over a field is not smooth. -/
theorem squareMap_not_smooth (k : Type u) [Field k] : ¬ Smooth (squareMap k) := sorry

/-- The squaring endomorphism of the affine line over a field is universally closed. -/
instance squareMap_universallyClosed (k : Type u) [Field k] :
    UniversallyClosed (squareMap k) := sorry

end AlgebraicGeometry.AffineSpace
