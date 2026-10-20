module

public import Mathlib.LinearAlgebra.FiniteDimensional.Defs
public import ReasLib.AlgebraicGeometry.FormalDeformation.FormalHomotopy
public import ReasLib.AlgebraicGeometry.FormalDeformation.FormalObject.Versal
public import ReasLib.AlgebraicGeometry.FormalDeformation.DeformationCategory
public import ReasLib.AlgebraicGeometry.FormalDeformation.InfinitesimalAutomorphisms.Unpointed
public import ReasLib.AlgebraicGeometry.FormalDeformation.TangentSpace.Tensor
public import ReasLib.AlgebraicGeometry.FormalDeformation.RimSchlessinger.Schlessinger
public import ReasLib.AlgebraicGeometry.FormalDeformation.Schlessinger.FiberIsoClass

@[expose] public section

open CategoryTheory ArtinianLocalAlgCat CompleteLocalAlgCat Functor

universe u

variable {Λ k : Type u} [CommRing Λ] [IsNoetherianRing Λ] [Field k] [Algebra Λ k]
  [Module.Finite Λ k]
variable {F : Type (u + 1)} [Category.{u + 1} F]
variable {p : F ⥤ ArtinianLocalAlgCat Λ k}

namespace CompleteLocalAlgCat

/-- In a deformation category with finite-dimensional tangent and infinitesimal
automorphism spaces, two base maps admitting lifts from a versal formal object
to a common formal object are formally homotopic. -/
theorem FormallyHomotopic.of_isVersal
    [Functor.IsDeformationCategory p]
    [FiniteDimensional k ((Functor.fiberIsoClassFunctor p).obj
      (ArtinianLocalAlgCat.dualNumber Λ k))]
    [FiniteDimensional k (Functor.infinitesimalAutomorphisms p)]
    (ξ : FormalObject p) [FormalObject.IsVersal ξ]
    (η : FormalObject p) {f g : ξ.base ⟶ η.base}
    (hf : ∃ a : ξ ⟶ η, a.base = f) (hg : ∃ b : ξ ⟶ η, b.base = g) :
    FormallyHomotopic f g := sorry

/-- In a deformation category with finite-dimensional tangent and infinitesimal
automorphism spaces, morphisms from a versal formal object to a common formal
object have formally homotopic base maps. -/
theorem FormallyHomotopic.of_isVersal_hom
    [Functor.IsDeformationCategory p]
    [FiniteDimensional k ((Functor.fiberIsoClassFunctor p).obj
      (ArtinianLocalAlgCat.dualNumber Λ k))]
    [FiniteDimensional k (Functor.infinitesimalAutomorphisms p)]
    (ξ : FormalObject p) [FormalObject.IsVersal ξ]
    (η : FormalObject p) (a b : ξ ⟶ η) :
    FormallyHomotopic a.base b.base := sorry

end CompleteLocalAlgCat
