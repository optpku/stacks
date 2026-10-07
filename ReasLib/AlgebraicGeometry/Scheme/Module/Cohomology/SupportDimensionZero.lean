module

public import ReasLib.AlgebraicGeometry.Scheme.Module.Cohomology.EulerCharacteristic
public import ReasLib.AlgebraicGeometry.Scheme.Module.Coherent.SupportDimensionZero
public import ReasLib.AlgebraicGeometry.Scheme.Module.Coherent.Tensor
public import ReasLib.AlgebraicGeometry.Scheme.Module.Stalk.OverSpec

/-!
# Cohomology of coherent modules with zero-dimensional support

This file records global generation, stalk decomposition, cohomology vanishing, and Euler
characteristic formulas for coherent modules with zero-dimensional support on schemes proper over
a field.
-/

@[expose] public section

open AlgebraicGeometry
open CategoryTheory
open CategoryTheory.Limits
open CategoryTheory.MonoidalCategory
open scoped DirectSum

noncomputable section

universe u

namespace AlgebraicGeometry.Scheme.Modules.SupportDimensionZero

variable {k : Type u} [Field k]
variable {X : Scheme.{u}}

/-- A coherent module with zero-dimensional support on a scheme proper over a field is generated
by global sections. -/
theorem isGloballyGenerated_of_isProper
    (f : X ⟶ Spec (CommRingCat.of k)) [IsProper f]
    (ℱ : X.Modules) [ℱ.IsCoherent]
    (hSuppDim : topologicalKrullDim (moduleSupport ℱ) ≤ 0) :
    SheafOfModules.IsGloballyGenerated ℱ := sorry

/-- Degree-zero cohomology of a coherent module with zero-dimensional support on a scheme proper
over a field is isomorphic, as a module over the field, to the direct sum of its support stalks. -/
theorem zeroCohomology_isomorphic_directSum_stalks
    (f : X ⟶ Spec (CommRingCat.of k)) [IsProper f]
    (ℱ : X.Modules) [ℱ.IsCoherent]
    (hSuppDim : topologicalKrullDim (moduleSupport ℱ) ≤ 0) :
    IsIsomorphic (Scheme.Hom.cohomology f ℱ 0)
      (ModuleCat.of k (Π₀ x : moduleSupport ℱ, Scheme.Hom.stalkMod f ℱ x)) := sorry

/-- Positive-degree cohomology of a coherent module with zero-dimensional support on a scheme
proper over a field vanishes. -/
theorem higherCohomology_isZero_of_isProper
    (f : X ⟶ Spec (CommRingCat.of k)) [IsProper f]
    (ℱ : X.Modules) [ℱ.IsCoherent]
    (hSuppDim : topologicalKrullDim (moduleSupport ℱ) ≤ 0)
    (i : ℕ) (hi : 0 < i) :
    IsZero (Scheme.Hom.cohomology f ℱ i) := sorry

/-- The Euler characteristic of a coherent module with zero-dimensional support on a scheme
proper over a field is the dimension of its degree-zero cohomology. -/
theorem eulerCharacteristic_eq_zeroCohomologyFinrank
    (f : X ⟶ Spec (CommRingCat.of k)) [IsProper f]
    (ℱ : X.Modules) [ℱ.IsCoherent]
    (hSuppDim : topologicalKrullDim (moduleSupport ℱ) ≤ 0) :
    Scheme.Hom.eulerCharacteristic f ℱ =
      (Scheme.Hom.cohomologyFinrank f ℱ 0 : ℤ) := sorry

/-- Tensoring a coherent module with zero-dimensional support by a finite locally free module of
constant rank multiplies its Euler characteristic by that rank. -/
theorem eulerCharacteristic_tensor_eq_rank_mul
    (f : X ⟶ Spec (CommRingCat.of k)) [IsProper f]
    (ℱ : X.Modules) [ℱ.IsCoherent]
    (hSuppDim : topologicalKrullDim (moduleSupport ℱ) ≤ 0)
    (n : ℕ) (ℰ : X.Modules) [IsFiniteLocallyFreeOfRank n ℰ] :
    -- Local instance justification (search instability): tensor coherence depends on the explicit
    -- proper structure morphism, which typeclass search cannot infer from the tensor module.
    let _ : (ℱ ⊗ ℰ : X.Modules).IsCoherent :=
      isCoherent_tensor_of_isProper_over_field f ℱ n ℰ
    Scheme.Hom.eulerCharacteristic f (ℱ ⊗ ℰ : X.Modules) =
      (n : ℤ) * Scheme.Hom.eulerCharacteristic f ℱ := sorry

end AlgebraicGeometry.Scheme.Modules.SupportDimensionZero
