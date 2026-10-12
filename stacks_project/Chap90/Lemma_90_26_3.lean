/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import Mathlib.LinearAlgebra.FiniteDimensional.Defs
public import stacks_project.Chap90.Definition_90_6_1_Prorepresentable
public import stacks_project.Chap90.Definition_90_16_8
public import stacks_project.Chap90.Definition_90_22_1_Prorepresentable
public import stacks_project.Chap90.Lemma_90_20_1_LinearMap
public import stacks_project.Chap90.Lemma_90_25_2
public import stacks_project.Chap90.Remark_90_19_4_InfinitesimalAut
import Mathlib.Tactic.CrossRefAttribute

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

/-- Lemma 90.26.3: if `F` is a deformation category, `U` is a prorepresentable functor
on `ArtinianLocalAlgCat Λ k`, and `f : U ⟶ F` is a morphism of categories cofibered in
groupoids, then the kernel-pair groupoid `ofMorphism f` constructed in Lemma 90.25.2 is
prorepresentable whenever `FiniteDimensional k (infinitesimalAutomorphisms F.p)`, i.e.
whenever `dim_k Inf(F)` is finite. -/
@[stacks 06L7]
instance instIsProrepresentable_ofMorphism
    (f : Functor.ofTypeValued.{u + 1, u, u} U ⟶ F)
    [IsDeformationCategory F.p] [Functor.IsProrepresentable U]
    [FiniteDimensional k (infinitesimalAutomorphisms F.p)] :
    IsProrepresentable (ofMorphism.{u + 1, u, u} f) := sorry

end CategoryTheory.GroupoidInFunctors
