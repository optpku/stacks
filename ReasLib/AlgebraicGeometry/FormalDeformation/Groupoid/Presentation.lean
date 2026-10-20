/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import Mathlib.LinearAlgebra.FiniteDimensional.Defs
public import ReasLib.AlgebraicGeometry.FormalDeformation.Groupoid.Prorepresentable
public import ReasLib.AlgebraicGeometry.FormalDeformation.SmoothGroupoid
public import ReasLib.CategoryTheory.Groupoid.InFunctors.Presentation
public import ReasLib.AlgebraicGeometry.FormalDeformation.InfinitesimalAutomorphisms.Unpointed
public import ReasLib.AlgebraicGeometry.FormalDeformation.TangentSpace.Tensor
public import ReasLib.AlgebraicGeometry.FormalDeformation.Schlessinger.FiberIsoClass
public import ReasLib.AlgebraicGeometry.FormalDeformation.RimSchlessinger.Schlessinger
public import ReasLib.AlgebraicGeometry.FormalDeformation.DeformationCategory.TwoFibreProduct

/-!
# Smooth prorepresentable presentations

A category cofibered in groupoids over Artinian local algebras admits a smooth
prorepresentable presentation exactly when it is a deformation category with
finite-dimensional tangent and infinitesimal automorphism spaces.
-/

@[expose] public section

noncomputable section

open CategoryTheory
open Functor
open ArtinianLocalAlgCat
open scoped Bicategory BasedFunctor

universe u

variable {Λ k : Type u} [CommRing Λ] [IsNoetherianRing Λ] [Field k] [Algebra Λ k]
  [Module.Finite Λ k]

namespace CategoryTheory.GroupoidInFunctors

variable {F : CofiberedCategoryOver.Groupoids.{u + 1, u, u + 1, u}
    (ArtinianLocalAlgCat Λ k)}
variable {G : GroupoidInFunctors.{u + 1, u, u} (ArtinianLocalAlgCat Λ k)}

/-- A category cofibered in groupoids with a smooth prorepresentable presentation
over Artinian local algebras is a deformation category. -/
theorem isDeformationCategory_of_isPresentation (φ : G.quotient ⟶ F)
    [IsSmooth G.s G.t] [IsProrepresentable G] (hφ : IsPresentation G F φ) :
    IsDeformationCategory F.p := sorry

/-- The tangent space of a deformation category with a smooth prorepresentable
presentation is finite-dimensional over the residue field. -/
theorem finiteDimensional_tangentSpace_of_isPresentation (φ : G.quotient ⟶ F)
    [IsSmooth G.s G.t] [IsProrepresentable G] [IsDeformationCategory F.p]
    (hφ : IsPresentation G F φ) :
    FiniteDimensional k ((fiberIsoClassFunctor F.p).obj (dualNumber Λ k)) := sorry

/-- The infinitesimal automorphism space of a deformation category with a smooth
prorepresentable presentation is finite-dimensional over the residue field. -/
theorem finiteDimensional_infinitesimalAutomorphisms_of_isPresentation
    (φ : G.quotient ⟶ F) [IsSmooth G.s G.t] [IsProrepresentable G]
    [IsDeformationCategory F.p] (hφ : IsPresentation G F φ) :
    FiniteDimensional k (infinitesimalAutomorphisms F.p) := sorry

/-- A deformation category with finite-dimensional tangent and infinitesimal
automorphism spaces admits a smooth prorepresentable presentation over the base. -/
theorem exists_smoothProrepresentablePresentation
    (F : CofiberedCategoryOver.Groupoids.{u + 1, u, u + 1, u}
      (ArtinianLocalAlgCat Λ k))
    [IsDeformationCategory F.p]
    [FiniteDimensional k ((fiberIsoClassFunctor F.p).obj (dualNumber Λ k))]
    [FiniteDimensional k (infinitesimalAutomorphisms F.p)] :
    ∃ (G : GroupoidInFunctors.{u + 1, u, u} (ArtinianLocalAlgCat Λ k))
      (φ : G.quotient ⟶ F),
      IsSmooth G.s G.t ∧ IsProrepresentable G ∧ IsPresentation G F φ := sorry

/-- A category cofibered in groupoids admits a smooth prorepresentable presentation
over Artinian local algebras if and only if it is a deformation category with
finite-dimensional tangent and infinitesimal automorphism spaces. -/
theorem exists_smoothProrepresentablePresentation_iff
    (F : CofiberedCategoryOver.Groupoids.{u + 1, u, u + 1, u}
      (ArtinianLocalAlgCat Λ k)) :
    (∃ (G : GroupoidInFunctors.{u + 1, u, u} (ArtinianLocalAlgCat Λ k))
      (φ : G.quotient ⟶ F),
      IsSmooth G.s G.t ∧ IsProrepresentable G ∧ IsPresentation G F φ) ↔
      IsDeformationCategory F.p ∧
        (∀ [IsDeformationCategory F.p],
          FiniteDimensional k ((fiberIsoClassFunctor F.p).obj (dualNumber Λ k)) ∧
            FiniteDimensional k (infinitesimalAutomorphisms F.p)) := sorry

end CategoryTheory.GroupoidInFunctors
