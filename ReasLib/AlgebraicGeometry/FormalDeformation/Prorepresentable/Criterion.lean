module

public import ReasLib.AlgebraicGeometry.FormalDeformation.Prorepresentable
public import ReasLib.AlgebraicGeometry.FormalDeformation.DeformationFunctor
public import ReasLib.AlgebraicGeometry.FormalDeformation.Predeformation.Derivation
public import Mathlib.LinearAlgebra.FiniteDimensional.Defs

/-!
# A tangent-space criterion for prorepresentability

Prorepresentability is characterized by deformation, finite-dimensional tangent
space, and injectivity of the canonical derivation-to-tangent map.
-/

@[expose] public section

open CategoryTheory
open Functor.IsPredeformationFunctor

universe u

variable {Λ k : Type u} [CommRing Λ] [IsNoetherianRing Λ] [Field k] [Algebra Λ k]
  [Module.Finite Λ k]

namespace CategoryTheory.Functor

/-- A functor on Artinian local algebras is prorepresentable exactly when it is a
deformation functor with finite-dimensional tangent space and injective canonical
derivation-to-tangent map. -/
theorem isProrepresentable_iff_finiteDimensional_ofDerivation
    (F : ArtinianLocalAlgCat Λ k ⥤ Type u) :
    IsProrepresentable F ↔
      IsDeformationFunctor F ∧
        (∀ [IsDeformationFunctor F],
          FiniteDimensional k (tangentSpace F) ∧
          Function.Injective (ofDerivation F)) := sorry

end CategoryTheory.Functor
