module

public import ReasLib.AlgebraicGeometry.FormalDeformation.Schlessinger
public import ReasLib.AlgebraicGeometry.FormalDeformation.Predeformation
public import ReasLib.AlgebraicGeometry.FormalDeformation.FormalObject.Versal

/-!
# Versal formal objects and Schlessinger's condition

A predeformation category admitting a versal formal object satisfies
Schlessinger's condition (S1).
-/

@[expose] public section

open CategoryTheory

universe u

variable {Λ k : Type u} [CommRing Λ] [IsNoetherianRing Λ] [Field k] [Algebra Λ k]
  [Module.Finite Λ k]
variable {F : Type (u + 1)} [Category.{u + 1} F]

namespace CategoryTheory.Functor

/-- A predeformation category with a versal formal object satisfies Schlessinger's
condition (S1). -/
theorem hasSchlessingerS1_of_isVersal (p : F ⥤ ArtinianLocalAlgCat Λ k)
    [IsPredeformationCategory p] (ξ : FormalObject p) [FormalObject.IsVersal ξ] :
    HasSchlessingerS1 p := sorry

end CategoryTheory.Functor
