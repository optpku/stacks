/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import Mathlib.FieldTheory.Separable
public import Mathlib.LinearAlgebra.FiniteDimensional.Defs
public import ReasLib.Algebra.Algebra.ResidueImage
public import ReasLib.AlgebraicGeometry.FormalDeformation.FormalObject.Differential
public import ReasLib.AlgebraicGeometry.FormalDeformation.FormalObject.Versal
public import ReasLib.AlgebraicGeometry.FormalDeformation.Schlessinger.FiberIsoClass
public import ReasLib.AlgebraicGeometry.FormalDeformation.TangentSpace.Tensor

/-!
# Hulls of formal objects

A hull is a versal formal object whose differential is bijective. Under the
classical or separable hypotheses, Schlessinger's conditions and a finite
dimensional tangent space give existence of a hull.
-/

@[expose] public section

open CategoryTheory Limits

universe u

variable {Λ k : Type u} [CommRing Λ] [IsNoetherianRing Λ] [Field k] [Algebra Λ k]
  [Module.Finite Λ k]

namespace CategoryTheory.Functor

/-- The identity projection of a complete local algebra has the residue-fibre
properties required of a predeformation category. -/
instance instIsPredeformationCategory_identityProjection
    (R : CompleteLocalAlgCat Λ k) :
    IsPredeformationCategory (CompleteLocalAlgCat.identityProjection R) := by
  sorry

end CategoryTheory.Functor

namespace FormalObject

variable {F : Type (u + 1)} [Category.{u + 1} F]
variable {p : F ⥤ ArtinianLocalAlgCat Λ k}

/-- Hullhood combines versality with bijectivity of the canonical differential. -/
class IsHull (ξ : FormalObject p) [Functor.IsPredeformationCategory p] : Prop
    extends IsVersal ξ where
  /-- The differential of a hull is bijective. -/
  bijective_differential : BijectiveDifferential ξ

/-- A formal object is a hull precisely when it is versal and has bijective differential. -/
theorem isHull_iff (ξ : FormalObject p) [Functor.IsPredeformationCategory p] :
    IsHull ξ ↔ IsVersal ξ ∧ BijectiveDifferential ξ := by
  constructor
  · intro h
    exact ⟨h.toIsVersal, h.bijective_differential⟩
  · rintro ⟨h_versal, h_bijective⟩
    exact { toIsVersal := h_versal, bijective_differential := h_bijective }

/-- The canonical differential of a hull is bijective. -/
theorem IsHull.spec (ξ : FormalObject p) [Functor.IsPredeformationCategory p]
    [IsHull ξ] : BijectiveDifferential ξ :=
  IsHull.bijective_differential

end FormalObject

namespace CompleteLocalAlgCat

/-- The identity formal object of a complete local algebra is a hull. -/
instance instIsHullIdentityFormalObject (R : CompleteLocalAlgCat Λ k) :
    FormalObject.IsHull (identityFormalObject R) := by
  sorry

end CompleteLocalAlgCat

namespace CategoryTheory.Functor

/-- A predeformation functor satisfying Schlessinger's conditions and having a
finite-dimensional canonical tangent space admits a hull in the classical case. -/
theorem exists_isHull (F : ArtinianLocalAlgCat Λ k ⥤ Type u)
    [IsPredeformationCategory (FormalObject.elementsProjectionULift F)]
    [HasSchlessingerS1 (FormalObject.elementsProjectionULift F)]
    [HasSchlessingerS2 (FormalObject.elementsProjectionULift F)]
    [FiniteDimensional k
      ((fiberIsoClassFunctor (FormalObject.elementsProjectionULift F)).obj
        (ArtinianLocalAlgCat.dualNumber Λ k))]
    [ArtinianLocalAlgCat.IsClassical Λ k] :
    ∃ ξ : FormalObject (FormalObject.elementsProjectionULift F), FormalObject.IsHull ξ := by
  sorry

/-- If the residue-image extension is separable, the same hypotheses admit a hull. -/
theorem exists_isHull_of_isSeparable (F : ArtinianLocalAlgCat Λ k ⥤ Type u)
    [IsPredeformationCategory (FormalObject.elementsProjectionULift F)]
    [HasSchlessingerS1 (FormalObject.elementsProjectionULift F)]
    [HasSchlessingerS2 (FormalObject.elementsProjectionULift F)]
    [FiniteDimensional k
      ((fiberIsoClassFunctor (FormalObject.elementsProjectionULift F)).obj
        (ArtinianLocalAlgCat.dualNumber Λ k))]
    [Algebra.IsSeparable (Algebra.residueImage Λ k) k] :
    ∃ ξ : FormalObject (FormalObject.elementsProjectionULift F), FormalObject.IsHull ξ := by
  sorry

end CategoryTheory.Functor
