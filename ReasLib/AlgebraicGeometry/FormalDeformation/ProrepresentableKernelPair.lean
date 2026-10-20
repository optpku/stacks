/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import Mathlib.LinearAlgebra.FiniteDimensional.Defs
public import ReasLib.AlgebraicGeometry.FormalDeformation.DeformationCategory.TwoFibreProduct
public import ReasLib.AlgebraicGeometry.FormalDeformation.Groupoid.Prorepresentable
public import ReasLib.CategoryTheory.Groupoid.KernelPair
public import ReasLib.AlgebraicGeometry.FormalDeformation.InfinitesimalAutomorphisms.Unpointed

/-!
# Prorepresentable kernel-pair presentations

A morphism from a prorepresentable functor to a deformation category with
finite-dimensional infinitesimal automorphism space yields a prorepresentable
kernel-pair groupoid in functors.
-/

@[expose] public section

noncomputable section

open CategoryTheory
open Functor

universe u

variable {Λ k : Type u} [CommRing Λ] [IsNoetherianRing Λ] [Field k] [Algebra Λ k]
  [Module.Finite Λ k]
variable {U : ArtinianLocalAlgCat Λ k ⥤ Type u}
variable {F : CofiberedCategoryOver.Groupoids.{u + 1, u, u + 1, u}
    (ArtinianLocalAlgCat Λ k)}

namespace CategoryTheory.GroupoidInFunctors

/-- The object and relation functors of the kernel-pair groupoid of a morphism
from a prorepresentable functor to a deformation category are prorepresentable
when the target's infinitesimal automorphism space is finite-dimensional. -/
theorem isProrepresentable_ofMorphism
    (f : Functor.ofTypeValued.{u + 1, u, u} U ⟶ F)
    [IsDeformationCategory F.p] [Functor.IsProrepresentable U]
    [FiniteDimensional k (infinitesimalAutomorphisms F.p)] :
    IsProrepresentable (ofMorphism.{u + 1, u, u} f) := sorry

end CategoryTheory.GroupoidInFunctors
