module

public import ReasLib.AlgebraicGeometry.Scheme.Module.WeaklyAssociatedPoints.FiniteGeneration
public import ReasLib.AlgebraicGeometry.Scheme.Module.WeaklyAssociatedPoints.Injectivity

/-!
# Injectivity from associated points

This module gives a criterion for a morphism of quasicoherent modules on a locally Noetherian
scheme to be a monomorphism by testing injectivity at associated points.
-/

@[expose] public section

open CategoryTheory
open AlgebraicGeometry

universe u

namespace AlgebraicGeometry.Scheme.Modules

/-- A morphism of quasicoherent modules on a locally Noetherian scheme is a monomorphism if its
stalk map is injective at every associated point of its source. -/
theorem mono_of_stalkwise_injective_or_not_mem_associatedPoints
    {X : Scheme.{u}} [IsLocallyNoetherian X]
    {ℱ 𝒢 : X.Modules} [ℱ.IsQuasicoherent] [𝒢.IsQuasicoherent]
    (φ : ℱ ⟶ 𝒢)
    (hφ : ∀ x : X,
      Function.Injective (RingedSpace.moduleStalkHom x φ) ∨ x ∉ associatedPoints ℱ) :
    Mono φ := sorry

end AlgebraicGeometry.Scheme.Modules
