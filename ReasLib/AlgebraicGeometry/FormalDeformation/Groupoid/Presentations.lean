module

public import Mathlib.FieldTheory.Separable
public import ReasLib.Algebra.Algebra.ResidueImage
public import ReasLib.AlgebraicGeometry.FormalDeformation.Groupoid.Presentation
public import ReasLib.AlgebraicGeometry.FormalDeformation.Groupoid.Rigidity
public import ReasLib.CategoryTheory.Cofibered.InGroupoids

/-!
# Minimal and normalized smooth prorepresentable presentations

Minimal smooth prorepresentable presentations exist exactly for deformation
categories with finite-dimensional tangent and infinitesimal automorphism
spaces, and are unique up to isomorphism. Normalized presentations imply these
conditions, with a converse when the residue field is separable over the image
of the base ring.
-/

@[expose] public section

open CategoryTheory
open Functor
open ArtinianLocalAlgCat
open scoped BasedFunctor

noncomputable section

universe u

variable {Λ k : Type u} [CommRing Λ] [IsNoetherianRing Λ] [Field k] [Algebra Λ k]
  [Module.Finite Λ k]

namespace CategoryTheory.GroupoidInFunctors

/-- Two minimal smooth prorepresentable groupoids in functors on
`ArtinianLocalAlgCat Λ k` presenting the same category cofibered in groupoids
are isomorphic. -/
theorem nonempty_iso_of_minimalPresentations
    (F : CofiberedCategoryOver.Groupoids.{u + 1, u, u + 1, u}
      (ArtinianLocalAlgCat Λ k))
    (G H : GroupoidInFunctors.{u + 1, u, u} (ArtinianLocalAlgCat Λ k))
    [IsSmooth G.s G.t] [IsProrepresentable G] [IsMinimal G]
    [IsSmooth H.s H.t] [IsProrepresentable H] [IsMinimal H]
    (φ : BasedCategory.ofFunctor G.forget ⥤ᵇ F.toBasedCategory)
    (ψ : BasedCategory.ofFunctor H.forget ⥤ᵇ F.toBasedCategory)
    [BasedFunctor.IsEquivalence φ] [BasedFunctor.IsEquivalence ψ] :
    Nonempty (Iso G H) := sorry

/-- A deformation category with finite-dimensional tangent and infinitesimal
automorphism spaces admits a minimal smooth prorepresentable presentation. -/
theorem exists_minimalSmoothProrepresentablePresentation
    (F : CofiberedCategoryOver.Groupoids.{u + 1, u, u + 1, u}
      (ArtinianLocalAlgCat Λ k))
    [IsDeformationCategory F.p]
    [FiniteDimensional k ((fiberIsoClassFunctor F.p).obj (dualNumber Λ k))]
    [FiniteDimensional k (infinitesimalAutomorphisms F.p)] :
    ∃ (G : GroupoidInFunctors.{u + 1, u, u} (ArtinianLocalAlgCat Λ k))
      (hSmooth : IsSmooth G.s G.t) (hPro : IsProrepresentable G)
      (hMin : IsMinimal G (smooth := hSmooth) (prorepresentable := hPro))
      (φ : G.quotient ⟶ F), IsPresentation G F φ := sorry

/-- A category cofibered in groupoids admits a minimal smooth prorepresentable
presentation if and only if it is a deformation category with finite-dimensional
tangent and infinitesimal automorphism spaces. -/
theorem exists_minimalSmoothProrepresentablePresentation_iff
    (F : CofiberedCategoryOver.Groupoids.{u + 1, u, u + 1, u}
      (ArtinianLocalAlgCat Λ k)) :
    (∃ (G : GroupoidInFunctors.{u + 1, u, u} (ArtinianLocalAlgCat Λ k))
      (hSmooth : IsSmooth G.s G.t) (hPro : IsProrepresentable G)
      (hMin : IsMinimal G (smooth := hSmooth) (prorepresentable := hPro))
      (φ : G.quotient ⟶ F), IsPresentation G F φ) ↔
      IsDeformationCategory F.p ∧
        (∀ [IsDeformationCategory F.p],
          FiniteDimensional k ((fiberIsoClassFunctor F.p).obj (dualNumber Λ k)) ∧
            FiniteDimensional k (infinitesimalAutomorphisms F.p)) := sorry

/-- Existence of a minimal smooth prorepresentable presentation is equivalent to
existence of a smooth prorepresentable presentation. -/
theorem exists_minimalSmoothProrepresentablePresentation_iff_exists_smooth
    (F : CofiberedCategoryOver.Groupoids.{u + 1, u, u + 1, u}
      (ArtinianLocalAlgCat Λ k)) :
    (∃ (G : GroupoidInFunctors.{u + 1, u, u} (ArtinianLocalAlgCat Λ k))
      (hSmooth : IsSmooth G.s G.t) (hPro : IsProrepresentable G)
      (hMin : IsMinimal G (smooth := hSmooth) (prorepresentable := hPro))
      (φ : G.quotient ⟶ F), IsPresentation G F φ) ↔
      ∃ (G : GroupoidInFunctors.{u + 1, u, u} (ArtinianLocalAlgCat Λ k))
        (φ : G.quotient ⟶ F),
        IsSmooth G.s G.t ∧ IsProrepresentable G ∧ IsPresentation G F φ := sorry

/-- Existence of a normalized smooth prorepresentable presentation implies
existence of a minimal smooth prorepresentable presentation. -/
theorem exists_minimalSmoothProrepresentablePresentation_of_isNormalized
    (F : CofiberedCategoryOver.Groupoids.{u + 1, u, u + 1, u}
      (ArtinianLocalAlgCat Λ k)) :
    (∃ (G : GroupoidInFunctors.{u + 1, u, u} (ArtinianLocalAlgCat Λ k))
      (hSmooth : IsSmooth G.s G.t) (hPro : IsProrepresentable G)
      (hNorm : IsNormalized G (smooth := hSmooth) (prorepresentable := hPro))
      (φ : G.quotient ⟶ F), IsPresentation G F φ) →
      ∃ (G : GroupoidInFunctors.{u + 1, u, u} (ArtinianLocalAlgCat Λ k))
        (hSmooth : IsSmooth G.s G.t) (hPro : IsProrepresentable G)
        (hMin : IsMinimal G (smooth := hSmooth) (prorepresentable := hPro))
        (φ : G.quotient ⟶ F), IsPresentation G F φ := sorry

/-- If the residue field is separable over the image of the base ring, existence
of a minimal smooth prorepresentable presentation implies existence of a
normalized smooth prorepresentable presentation. -/
theorem exists_normalizedSmoothProrepresentablePresentation_of_isMinimal
    (F : CofiberedCategoryOver.Groupoids.{u + 1, u, u + 1, u}
      (ArtinianLocalAlgCat Λ k))
    [Algebra.IsSeparable (Algebra.residueImage Λ k) k] :
    (∃ (G : GroupoidInFunctors.{u + 1, u, u} (ArtinianLocalAlgCat Λ k))
      (hSmooth : IsSmooth G.s G.t) (hPro : IsProrepresentable G)
      (hMin : IsMinimal G (smooth := hSmooth) (prorepresentable := hPro))
      (φ : G.quotient ⟶ F), IsPresentation G F φ) →
      ∃ (G : GroupoidInFunctors.{u + 1, u, u} (ArtinianLocalAlgCat Λ k))
        (hSmooth : IsSmooth G.s G.t) (hPro : IsProrepresentable G)
        (hNorm : IsNormalized G (smooth := hSmooth) (prorepresentable := hPro))
        (φ : G.quotient ⟶ F), IsPresentation G F φ := sorry

/-- If the residue field is separable over the image of the base ring, a category
cofibered in groupoids admits a normalized smooth prorepresentable presentation
if and only if it is a deformation category with finite-dimensional tangent and
infinitesimal automorphism spaces. -/
theorem exists_normalizedSmoothProrepresentablePresentation_iff
    (F : CofiberedCategoryOver.Groupoids.{u + 1, u, u + 1, u}
      (ArtinianLocalAlgCat Λ k))
    [Algebra.IsSeparable (Algebra.residueImage Λ k) k] :
    (∃ (G : GroupoidInFunctors.{u + 1, u, u} (ArtinianLocalAlgCat Λ k))
      (hSmooth : IsSmooth G.s G.t) (hPro : IsProrepresentable G)
      (hNorm : IsNormalized G (smooth := hSmooth) (prorepresentable := hPro))
      (φ : G.quotient ⟶ F), IsPresentation G F φ) ↔
      IsDeformationCategory F.p ∧
        (∀ [IsDeformationCategory F.p],
          FiniteDimensional k ((fiberIsoClassFunctor F.p).obj (dualNumber Λ k)) ∧
            FiniteDimensional k (infinitesimalAutomorphisms F.p)) := sorry

end CategoryTheory.GroupoidInFunctors
