/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.AlgebraicGeometry.FormalDeformation.Schlessinger.FiberIsoClass
public import ReasLib.AlgebraicGeometry.FormalDeformation.TangentSpace.Tensor
public import ReasLib.AlgebraicGeometry.FormalDeformation.FormalObject.Versal
public import ReasLib.AlgebraicGeometry.FormalDeformation.FormalObject.MinimalVersal
public import ReasLib.AlgebraicGeometry.FormalDeformation.FormalObject.Schlessinger
public import ReasLib.Algebra.Algebra.ResidueImage
public import Mathlib.FieldTheory.Separable
public import Mathlib.LinearAlgebra.FiniteDimensional.Defs

/-!
# Existence of versal and minimal versal formal objects

A predeformation category satisfying Schlessinger's first two conditions and
having finite-dimensional tangent space admits a versal formal object.
It also admits a minimal versal formal object with orbit-bijective differential.
Existence of a minimal versal formal object with bijective differential implies
these Schlessinger and finiteness conditions. Under separability of the residue
field over the residue image, bijectivity and orbit bijectivity coincide.
-/

@[expose] public section

open CategoryTheory ArtinianLocalAlgCat

universe u

variable {Λ k : Type u} [CommRing Λ] [IsNoetherianRing Λ] [Field k] [Algebra Λ k]
  [Module.Finite Λ k]
variable {F : Type (u + 1)} [Category.{u + 1} F]
variable {p : F ⥤ ArtinianLocalAlgCat Λ k}

namespace CategoryTheory.Functor

/-- A predeformation category satisfying (S1) and (S2) with finite-dimensional
tangent space admits a versal formal object. -/
theorem exists_isVersal (p : F ⥤ ArtinianLocalAlgCat Λ k)
    [IsPredeformationCategory p] [HasSchlessingerS1 p] [HasSchlessingerS2 p]
    [FiniteDimensional k ((fiberIsoClassFunctor p).obj (dualNumber Λ k))] :
    ∃ ξ : FormalObject p, FormalObject.IsVersal ξ := by
  sorry

/-- A predeformation category admitting a minimal versal formal object with
bijective differential satisfies Schlessinger's condition (S2). -/
theorem hasSchlessingerS2_of_isMinimalVersal_bijectiveDifferential
    [IsPredeformationCategory p] (ξ : FormalObject p)
    [minimal : FormalObject.IsMinimalVersal ξ]
    (h : FormalObject.BijectiveDifferential ξ) :
    HasSchlessingerS2 p := sorry

/-- The canonical tangent space of a predeformation category satisfying (S2) is
finite-dimensional if it admits a minimal versal formal object with bijective differential. -/
theorem finiteDimensional_tangentSpace_of_isMinimalVersal_bijectiveDifferential
    [IsPredeformationCategory p] [HasSchlessingerS2 p] (ξ : FormalObject p)
    [minimal : FormalObject.IsMinimalVersal ξ]
    (h : FormalObject.BijectiveDifferential ξ) :
    FiniteDimensional k ((fiberIsoClassFunctor p).obj (dualNumber Λ k)) := sorry

/-- Fact-certified existence of a minimal versal formal object with bijective
differential gives Schlessinger's condition (S2). -/
instance instHasSchlessingerS2OfMiniversalBijectiveDifferential
    (p : F ⥤ ArtinianLocalAlgCat Λ k) [IsPredeformationCategory p]
    [Fact (∃ ξ : FormalObject p,
      FormalObject.IsMinimalVersal ξ ∧ FormalObject.BijectiveDifferential ξ)] :
    HasSchlessingerS2 p := by
  obtain ⟨ξ, minimal, bijective⟩ :=
    (Fact.out : ∃ ξ : FormalObject p,
      FormalObject.IsMinimalVersal ξ ∧ FormalObject.BijectiveDifferential ξ)
  exact hasSchlessingerS2_of_isMinimalVersal_bijectiveDifferential
    ξ (minimal := minimal) bijective

/-- Fact-certified existence of a minimal versal formal object with bijective
differential makes the canonical tangent space finite-dimensional under (S2). -/
instance instFiniteDimensionalOfMiniversalBijectiveDifferential
    (p : F ⥤ ArtinianLocalAlgCat Λ k) [IsPredeformationCategory p]
    [HasSchlessingerS2 p]
    [Fact (∃ ξ : FormalObject p,
      FormalObject.IsMinimalVersal ξ ∧ FormalObject.BijectiveDifferential ξ)] :
    FiniteDimensional k ((fiberIsoClassFunctor p).obj (dualNumber Λ k)) := by
  obtain ⟨ξ, minimal, bijective⟩ :=
    (Fact.out : ∃ ξ : FormalObject p,
      FormalObject.IsMinimalVersal ξ ∧ FormalObject.BijectiveDifferential ξ)
  exact finiteDimensional_tangentSpace_of_isMinimalVersal_bijectiveDifferential
    ξ (minimal := minimal) bijective

end CategoryTheory.Functor

namespace FormalObject

/-- A predeformation category satisfying (S1) and (S2) with finite-dimensional
canonical tangent space admits a minimal versal formal object with orbit-bijective differential. -/
theorem exists_isMinimalVersal_bijectiveDifferentialOnOrbits
    [Functor.IsPredeformationCategory p] [Functor.HasSchlessingerS1 p]
    [Functor.HasSchlessingerS2 p]
    [FiniteDimensional k ((Functor.fiberIsoClassFunctor p).obj (dualNumber Λ k))] :
    ∃ ξ : FormalObject p, IsMinimalVersal ξ ∧ BijectiveDifferentialOnOrbits ξ := sorry

/-- Over a residue field separable over the residue image, a formal object's
differential is bijective if and only if it is bijective on residue-derivation orbits. -/
theorem bijectiveDifferential_iff_bijectiveDifferentialOnOrbits
    [Functor.IsPredeformationCategory p]
    [Algebra.IsSeparable (Algebra.residueImage Λ k) k] (ξ : FormalObject p) :
    BijectiveDifferential ξ ↔ BijectiveDifferentialOnOrbits ξ := sorry

/-- Over a residue field separable over the residue image, a predeformation
category satisfying (S1) and (S2) with finite-dimensional canonical tangent space
admits a minimal versal formal object with bijective differential. -/
theorem exists_isMinimalVersal_bijectiveDifferential
    [Functor.IsPredeformationCategory p] [Functor.HasSchlessingerS1 p]
    [Functor.HasSchlessingerS2 p]
    [FiniteDimensional k ((Functor.fiberIsoClassFunctor p).obj (dualNumber Λ k))]
    [Algebra.IsSeparable (Algebra.residueImage Λ k) k] :
    ∃ ξ : FormalObject p, IsMinimalVersal ξ ∧ BijectiveDifferential ξ := by
  obtain ⟨ξ, minimal, bijective⟩ :=
    exists_isMinimalVersal_bijectiveDifferentialOnOrbits (p := p)
  exact ⟨ξ, minimal, (bijectiveDifferential_iff_bijectiveDifferentialOnOrbits ξ).mpr bijective⟩

end FormalObject

namespace CategoryTheory.Functor

/-- A minimal versal formal object with bijective differential implies (S1),
(S2), and finite-dimensional canonical tangent space; these conditions imply
existence of a minimal versal formal object with orbit-bijective differential.
Over a residue field separable over the residue image, the two differential
conditions coincide for every formal object. -/
theorem miniversalExistence (p : F ⥤ ArtinianLocalAlgCat Λ k)
    [IsPredeformationCategory p] :
    ((∃ ξ : FormalObject p, FormalObject.IsMinimalVersal ξ ∧
        FormalObject.BijectiveDifferential ξ) →
      HasSchlessingerS1 p ∧ HasSchlessingerS2 p ∧
        (∀ [HasSchlessingerS2 p],
          FiniteDimensional k ((fiberIsoClassFunctor p).obj (dualNumber Λ k)))) ∧
    (∀ [HasSchlessingerS1 p] [HasSchlessingerS2 p]
        [FiniteDimensional k ((fiberIsoClassFunctor p).obj (dualNumber Λ k))],
      ∃ ξ : FormalObject p, FormalObject.IsMinimalVersal ξ ∧
        FormalObject.BijectiveDifferentialOnOrbits ξ) ∧
    (∀ [Algebra.IsSeparable (Algebra.residueImage Λ k) k] (ξ : FormalObject p),
      FormalObject.BijectiveDifferential ξ ↔
        FormalObject.BijectiveDifferentialOnOrbits ξ) := sorry

end CategoryTheory.Functor
