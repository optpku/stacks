/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.AlgebraicGeometry.FormalDeformation.Groupoid.Presentations
import StacksCheckRecall

/-!
# Minimal smooth prorepresentable presentations

Smooth and minimal smooth prorepresentable presentations are characterized by
the deformation-category property and finite-dimensional tangent and
infinitesimal automorphism spaces. Normalized presentations imply these
conditions, and are equivalent under separability over the residue image.
Minimal presenting groupoids are unique up to isomorphism.
-/

@[expose] public section

noncomputable section

open CategoryTheory
open Functor
open ArtinianLocalAlgCat
open scoped BasedFunctor

universe u

variable {Λ k : Type u} [CommRing Λ] [IsNoetherianRing Λ] [Field k] [Algebra Λ k]
  [Module.Finite Λ k]

namespace CategoryTheory.GroupoidInFunctors

/- Theorem 90.27.8: for a category cofibered in groupoids over
`ArtinianLocalAlgCat Λ k`, consider (1) existence of a normalized smooth
prorepresentable presentation, (2) existence of a smooth prorepresentable
presentation, (3) existence of a minimal smooth prorepresentable presentation,
and (4) the deformation-category property with finite-dimensional tangent and
infinitesimal automorphism spaces. Conditions (2), (3), and (4) are equivalent
and follow from (1). If `k` is separable over `Algebra.residueImage Λ k`, all
four conditions are equivalent. Minimal presenting groupoids are unique up to
isomorphism. -/
@[stacks 06TE] #check
  (CategoryTheory.GroupoidInFunctors.exists_minimalSmoothProrepresentablePresentation_iff :
    ∀ (F : CofiberedCategoryOver.Groupoids.{u + 1, u, u + 1, u}
      (ArtinianLocalAlgCat Λ k)),
    (∃ (G : GroupoidInFunctors.{u + 1, u, u} (ArtinianLocalAlgCat Λ k))
      (hSmooth : IsSmooth G.s G.t) (hPro : IsProrepresentable G)
      (hMin : IsMinimal G (smooth := hSmooth) (prorepresentable := hPro))
      (φ : G.quotient ⟶ F), IsPresentation G F φ) ↔
      IsDeformationCategory F.p ∧
        (∀ [IsDeformationCategory F.p],
          FiniteDimensional k ((fiberIsoClassFunctor F.p).obj (dualNumber Λ k)) ∧
            FiniteDimensional k (infinitesimalAutomorphisms F.p)))

#check
  (CategoryTheory.GroupoidInFunctors.exists_minimalSmoothProrepresentablePresentation :
    ∀ (F : CofiberedCategoryOver.Groupoids.{u + 1, u, u + 1, u}
      (ArtinianLocalAlgCat Λ k))
    [IsDeformationCategory F.p]
    [FiniteDimensional k ((fiberIsoClassFunctor F.p).obj (dualNumber Λ k))]
    [FiniteDimensional k (infinitesimalAutomorphisms F.p)],
    ∃ (G : GroupoidInFunctors.{u + 1, u, u} (ArtinianLocalAlgCat Λ k))
      (hSmooth : IsSmooth G.s G.t) (hPro : IsProrepresentable G)
      (hMin : IsMinimal G (smooth := hSmooth) (prorepresentable := hPro))
      (φ : G.quotient ⟶ F), IsPresentation G F φ)

#check
  (CategoryTheory.GroupoidInFunctors.exists_minimalSmoothProrepresentablePresentation_iff_exists_smooth :
    ∀ (F : CofiberedCategoryOver.Groupoids.{u + 1, u, u + 1, u}
      (ArtinianLocalAlgCat Λ k)),
    (∃ (G : GroupoidInFunctors.{u + 1, u, u} (ArtinianLocalAlgCat Λ k))
      (hSmooth : IsSmooth G.s G.t) (hPro : IsProrepresentable G)
      (hMin : IsMinimal G (smooth := hSmooth) (prorepresentable := hPro))
      (φ : G.quotient ⟶ F), IsPresentation G F φ) ↔
      ∃ (G : GroupoidInFunctors.{u + 1, u, u} (ArtinianLocalAlgCat Λ k))
        (φ : G.quotient ⟶ F),
        IsSmooth G.s G.t ∧ IsProrepresentable G ∧ IsPresentation G F φ)

#check
  (CategoryTheory.GroupoidInFunctors.exists_minimalSmoothProrepresentablePresentation_of_isNormalized :
    ∀ (F : CofiberedCategoryOver.Groupoids.{u + 1, u, u + 1, u}
      (ArtinianLocalAlgCat Λ k)),
    (∃ (G : GroupoidInFunctors.{u + 1, u, u} (ArtinianLocalAlgCat Λ k))
      (hSmooth : IsSmooth G.s G.t) (hPro : IsProrepresentable G)
      (hNorm : IsNormalized G (smooth := hSmooth) (prorepresentable := hPro))
      (φ : G.quotient ⟶ F), IsPresentation G F φ) →
      ∃ (G : GroupoidInFunctors.{u + 1, u, u} (ArtinianLocalAlgCat Λ k))
        (hSmooth : IsSmooth G.s G.t) (hPro : IsProrepresentable G)
        (hMin : IsMinimal G (smooth := hSmooth) (prorepresentable := hPro))
        (φ : G.quotient ⟶ F), IsPresentation G F φ)

#check
  (CategoryTheory.GroupoidInFunctors.exists_normalizedSmoothProrepresentablePresentation_of_isMinimal :
    ∀ (F : CofiberedCategoryOver.Groupoids.{u + 1, u, u + 1, u}
      (ArtinianLocalAlgCat Λ k))
    [Algebra.IsSeparable (Algebra.residueImage Λ k) k],
    (∃ (G : GroupoidInFunctors.{u + 1, u, u} (ArtinianLocalAlgCat Λ k))
      (hSmooth : IsSmooth G.s G.t) (hPro : IsProrepresentable G)
      (hMin : IsMinimal G (smooth := hSmooth) (prorepresentable := hPro))
      (φ : G.quotient ⟶ F), IsPresentation G F φ) →
      ∃ (G : GroupoidInFunctors.{u + 1, u, u} (ArtinianLocalAlgCat Λ k))
        (hSmooth : IsSmooth G.s G.t) (hPro : IsProrepresentable G)
        (hNorm : IsNormalized G (smooth := hSmooth) (prorepresentable := hPro))
        (φ : G.quotient ⟶ F), IsPresentation G F φ)

#check
  (CategoryTheory.GroupoidInFunctors.exists_normalizedSmoothProrepresentablePresentation_iff :
    ∀ (F : CofiberedCategoryOver.Groupoids.{u + 1, u, u + 1, u}
      (ArtinianLocalAlgCat Λ k))
    [Algebra.IsSeparable (Algebra.residueImage Λ k) k],
    (∃ (G : GroupoidInFunctors.{u + 1, u, u} (ArtinianLocalAlgCat Λ k))
      (hSmooth : IsSmooth G.s G.t) (hPro : IsProrepresentable G)
      (hNorm : IsNormalized G (smooth := hSmooth) (prorepresentable := hPro))
      (φ : G.quotient ⟶ F), IsPresentation G F φ) ↔
      IsDeformationCategory F.p ∧
        (∀ [IsDeformationCategory F.p],
          FiniteDimensional k ((fiberIsoClassFunctor F.p).obj (dualNumber Λ k)) ∧
            FiniteDimensional k (infinitesimalAutomorphisms F.p)))

#check
  (CategoryTheory.GroupoidInFunctors.nonempty_iso_of_minimalPresentations :
    ∀ (F : CofiberedCategoryOver.Groupoids.{u + 1, u, u + 1, u}
      (ArtinianLocalAlgCat Λ k))
    (G H : GroupoidInFunctors.{u + 1, u, u} (ArtinianLocalAlgCat Λ k))
    [IsSmooth G.s G.t] [IsProrepresentable G] [IsMinimal G]
    [IsSmooth H.s H.t] [IsProrepresentable H] [IsMinimal H]
    (φ : BasedCategory.ofFunctor G.forget ⥤ᵇ F.toBasedCategory)
    (ψ : BasedCategory.ofFunctor H.forget ⥤ᵇ F.toBasedCategory)
    [BasedFunctor.IsEquivalence φ] [BasedFunctor.IsEquivalence ψ],
    Nonempty (Iso G H))

end CategoryTheory.GroupoidInFunctors
