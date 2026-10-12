/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import Mathlib.LinearAlgebra.FiniteDimensional.Defs
public import stacks_project.Chap90.Definition_90_22_1_Prorepresentable
public import stacks_project.Chap90.Definition_90_23_1
public import stacks_project.Chap90.Definition_90_25_1
public import stacks_project.Chap90.Lemma_90_20_1_LinearMap
import Mathlib.Tactic.CrossRefAttribute

/-!
# Presentations of deformation categories

A category cofibered in groupoids over `ArtinianLocalAlgCat Λ k` admits a presentation
by a smooth prorepresentable groupoid in functors if and only if it is a deformation
category whose tangent space and infinitesimal automorphism space are finite-dimensional
over `k`.
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

/-- Theorem 90.26.4 (1): if `φ : G.quotient ⟶ F` is a presentation of the category
cofibered in groupoids `F` by a smooth prorepresentable groupoid in functors on
`ArtinianLocalAlgCat Λ k`, then `F.p` is a deformation category. -/
@[stacks 06L8]
theorem isDeformationCategory_of_isPresentation (φ : G.quotient ⟶ F)
    [IsSmooth G.s G.t] [IsProrepresentable G] (hφ : IsPresentation G F φ) :
    IsDeformationCategory F.p := sorry

/-- Theorem 90.26.4 (2): if `φ : G.quotient ⟶ F` is a presentation of the category
cofibered in groupoids `F` by a smooth prorepresentable groupoid in functors on
`ArtinianLocalAlgCat Λ k`, then `(fiberIsoClassFunctor F.p).obj (dualNumber Λ k)` is
finite-dimensional over `k`. -/
@[stacks 06L8]
theorem finiteDimensional_tangentSpace_of_isPresentation (φ : G.quotient ⟶ F)
    [IsSmooth G.s G.t] [IsProrepresentable G] [IsDeformationCategory F.p]
    (hφ : IsPresentation G F φ) :
    FiniteDimensional k ((fiberIsoClassFunctor F.p).obj (dualNumber Λ k)) := sorry

/-- Theorem 90.26.4 (3): if `φ : G.quotient ⟶ F` is a presentation of the category
cofibered in groupoids `F` by a smooth prorepresentable groupoid in functors on
`ArtinianLocalAlgCat Λ k`, then `infinitesimalAutomorphisms F.p` is finite-dimensional
over `k`. -/
@[stacks 06L8]
theorem finiteDimensional_infinitesimalAutomorphisms_of_isPresentation
    (φ : G.quotient ⟶ F) [IsSmooth G.s G.t] [IsProrepresentable G]
    [IsDeformationCategory F.p] (hφ : IsPresentation G F φ) :
    FiniteDimensional k (infinitesimalAutomorphisms F.p) := sorry

/-- Theorem 90.26.4 (4): if `F` is a deformation category over `ArtinianLocalAlgCat Λ k`
whose tangent space `(fiberIsoClassFunctor F.p).obj (dualNumber Λ k)` and infinitesimal
automorphism space `infinitesimalAutomorphisms F.p` are finite-dimensional over `k`,
then there exist a groupoid in functors `G` and a morphism `φ : G.quotient ⟶ F` which
is a presentation of `F` by a smooth prorepresentable groupoid in functors. -/
@[stacks 06L8]
theorem exists_smoothProrepresentablePresentation
    (F : CofiberedCategoryOver.Groupoids.{u + 1, u, u + 1, u}
      (ArtinianLocalAlgCat Λ k))
    [IsDeformationCategory F.p]
    [FiniteDimensional k ((fiberIsoClassFunctor F.p).obj (dualNumber Λ k))]
    [FiniteDimensional k (infinitesimalAutomorphisms F.p)] :
    ∃ (G : GroupoidInFunctors.{u + 1, u, u} (ArtinianLocalAlgCat Λ k))
      (φ : G.quotient ⟶ F),
      IsSmooth G.s G.t ∧ IsProrepresentable G ∧ IsPresentation G F φ := sorry

/-- Once `F` is a deformation category, it admits a presentation by a smooth
prorepresentable groupoid in functors if and only if
`(fiberIsoClassFunctor F.p).obj (dualNumber Λ k)` and
`infinitesimalAutomorphisms F.p` are finite-dimensional over `k`. -/
theorem exists_smoothProrepresentablePresentation_iff
    (F : CofiberedCategoryOver.Groupoids.{u + 1, u, u + 1, u}
      (ArtinianLocalAlgCat Λ k))
    [IsDeformationCategory F.p] :
    (∃ (G : GroupoidInFunctors.{u + 1, u, u} (ArtinianLocalAlgCat Λ k))
      (φ : G.quotient ⟶ F),
      IsSmooth G.s G.t ∧ IsProrepresentable G ∧ IsPresentation G F φ) ↔
      FiniteDimensional k ((fiberIsoClassFunctor F.p).obj (dualNumber Λ k)) ∧
        FiniteDimensional k (infinitesimalAutomorphisms F.p) := sorry

end CategoryTheory.GroupoidInFunctors
