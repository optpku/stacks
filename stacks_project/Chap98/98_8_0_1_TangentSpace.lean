/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import Mathlib.CategoryTheory.IsomorphismClasses
public import stacks_project.Chap98.«98_3_0_2_Category»

/-!
# Tangent space of `ℱ_{𝒳, k, x₀}`

The tangent space `Tℱ_{𝒳, k, x₀}` is the type of isomorphism classes of the
fibre of `ℱ_{𝒳, k, x₀}` over the dual numbers `k[ε]`.
-/

@[expose] public section

open CategoryTheory AlgebraicGeometry Functor

noncomputable section

universe u

namespace AlgebraicGeometry.GroupoidsOver.Predeformation

variable {S : Scheme.{u}} [IsLocallyNoetherian S]
variable {Λ k : Type u} [CommRing Λ] [IsNoetherianRing Λ] [Field k] [Algebra Λ k]
  [Module.Finite Λ k]
variable (openImmersion : Spec (CommRingCat.of Λ) ⟶ S) [IsOpenImmersion openImmersion]
variable (kToS : Spec (CommRingCat.of k) ⟶ S) [LocallyOfFiniteType kToS]
variable (h_factor : Spec.map (CommRingCat.ofHom (algebraMap Λ k)) ≫ openImmersion = kToS)
variable (X : FiberedCategoryOver.Groupoids.{u + 1, u, u + 1, u} (Over S))
variable (x0 : X.p.Fiber (Over.mk kToS))

/-- The fibre of `ℱ_{𝒳, k, x₀}` over the dual numbers `k[ε]`. -/
abbrev dualNumberFiber :=
  (forget openImmersion kToS h_factor X x0).Fiber (ArtinianLocalAlgCat.dualNumber Λ k)

/-- The tangent space of the predeformation category `ℱ_{𝒳, k, x₀}` is the type of
isomorphism classes of objects in the fibre over `ArtinianLocalAlgCat.dualNumber Λ k`. -/
def tangentSpace :=
  isomorphismClasses.obj (Cat.of (dualNumberFiber openImmersion kToS h_factor X x0))

/-- The isomorphism class of a morphism `x₀ ⟶ x` over `Spec(k) ⟶ Spec(k[ε])`. -/
def tangentSpace.mk (ξ : dualNumberFiber openImmersion kToS h_factor X x0) :
    tangentSpace openImmersion kToS h_factor X x0 :=
  Quotient.mk'' ξ

/-- Two dual-number fibre objects determine the same tangent vector if and only if they
are isomorphic in the fibre. -/
theorem tangentSpace.mk_eq_mk
    (ξ η : dualNumberFiber openImmersion kToS h_factor X x0) :
    tangentSpace.mk openImmersion kToS h_factor X x0 ξ =
        tangentSpace.mk openImmersion kToS h_factor X x0 η ↔
      Nonempty (ξ ≅ η) :=
  sorry

/-- The tangent space is the type of isomorphism classes of the dual-number fibre. -/
theorem tangentSpace_def :
    tangentSpace openImmersion kToS h_factor X x0 =
      isomorphismClasses.obj (Cat.of (dualNumberFiber openImmersion kToS h_factor X x0)) :=
  sorry

/-- The dual-number fibre is the fibre of `ℱ_{𝒳, k, x₀}` over `k[ε]`. -/
theorem dualNumberFiber_eq :
    dualNumberFiber openImmersion kToS h_factor X x0 =
      fiber openImmersion kToS h_factor X x0 (ArtinianLocalAlgCat.dualNumber Λ k) :=
  sorry

end AlgebraicGeometry.GroupoidsOver.Predeformation
