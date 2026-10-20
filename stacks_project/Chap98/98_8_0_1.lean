/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import stacks_project.Chap98.«98_8_0_1_TangentSpace»
import StacksCheckRecall
public import ReasLib.AlgebraicGeometry.FormalDeformation.TangentSpace

/-!
# Tangent space of a predeformation category associated to a residue object

The tangent space `Tℱ_{𝒳, k, x₀}` of `ℱ_{𝒳, k, x₀}` is the type of isomorphism
classes of morphisms `x₀ ⟶ x` over `Spec(k) ⟶ Spec(k[ε])`.
-/

@[expose] public section

open CategoryTheory AlgebraicGeometry
open AlgebraicGeometry.GroupoidsOver.Predeformation

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

/- 98.8.0.1: the tangent space `Tℱ_{𝒳, k, x₀}` of the predeformation category
`ℱ_{𝒳, k, x₀}` is the type of isomorphism classes of morphisms `x₀ ⟶ x` over
`Spec(k) ⟶ Spec(k[ε])`, recovered as the fibre of `ℱ_{𝒳, k, x₀}` over
`ArtinianLocalAlgCat.dualNumber Λ k` via `specOver_toResidue`. -/
@[stacks 07WZ] #check (CategoryTheory.Functor.tangentSpace_def
    (predeformationFunctor X openImmersion kToS h_factor x0) :
    tangentSpace openImmersion kToS h_factor X x0 =
      isomorphismClasses.obj (Cat.of (dualNumberFiber openImmersion kToS h_factor X x0)))

end AlgebraicGeometry.GroupoidsOver.Predeformation
