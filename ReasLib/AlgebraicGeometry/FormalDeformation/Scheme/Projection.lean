module

public import ReasLib.AlgebraicGeometry.FormalDeformation.Scheme

/-!
# The projection of a scheme deformation category
-/

@[expose] public section

open CategoryTheory AlgebraicGeometry Functor

universe u

namespace FlatSchemeCat

variable (Λ k : Type u) [CommRing Λ] [IsNoetherianRing Λ] [Field k] [Algebra Λ k]
  [Module.Finite Λ k]
variable (X : Scheme.{u}) (hX : X ⟶ Spec (CommRingCat.of k))

/-- The deformation category of a scheme projects to its Artinian local base algebras. -/
abbrev deformationForget : deformationCategory Λ k X hX ⥤ ArtinianLocalAlgCat Λ k :=
  Over.forget (Fiber.fiberInclusion.obj (residueObj Λ k X hX)) ⋙ forget Λ k

/-- The deformation projection sends an object to its base algebra. -/
theorem deformationForget_obj (x : deformationCategory Λ k X hX) :
    (deformationForget Λ k X hX).obj x = x.left.base := rfl

end FlatSchemeCat
