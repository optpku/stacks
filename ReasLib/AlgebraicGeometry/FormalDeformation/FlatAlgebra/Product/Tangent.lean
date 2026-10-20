module

public import ReasLib.AlgebraicGeometry.FormalDeformation.FlatAlgebra.Product
public import ReasLib.AlgebraicGeometry.FormalDeformation.FlatAlgebra.DualNumber
public import ReasLib.AlgebraicGeometry.FormalDeformation.Differential

/-!
# Tangent spaces of equibased algebra deformation products

The projection of equibased deformation families is a predeformation category,
and its tangent space is identified with the product of the factor tangent spaces.
-/

@[expose] public section

open CategoryTheory Functor
open scoped BasedFunctor

universe u

noncomputable section

namespace FlatAlgebraCat

variable (Λ k : Type u) [CommRing Λ] [IsNoetherianRing Λ] [Field k] [Algebra Λ k]
  [Module.Finite Λ k]
variable {ι : Type u}
variable {R : ι → Type u} [∀ i, CommRing (R i)] [∀ i, Algebra k (R i)]

variable (R) in
/-- The projection of equibased deformation families is a predeformation category. -/
instance instIsPredeformationCategory_deformationPiForget :
    IsPredeformationCategory (deformationPiForget Λ k R) := sorry

/-- The tangent space of `deformationPi` is the product of the tangent spaces of
the factors `Def_{R i}`. -/
theorem tangentSpace_deformationPi :
    Function.Bijective fun v : Functor.tangentSpace (deformationPiForget Λ k R) ↦
      fun i ↦ BasedFunctor.differential (evalBasedFunctor Λ k R i) v :=
  sorry

end FlatAlgebraCat

end
